Lesson 02: Closures and Stack Safety
====================================

In functional programming languages - such as Scala or Haskell -, the concepts of stack safety and monads are intimately
related - through a series of intermediary notions -, though independent. For instance, some recursive algorithms (such as
that computing the factorial of a number) can be transformed into loops if they are tail-recursive or can be made as such
(like having the result passed as an argument) - without the need of monads or anything related to them. Conversely, monads
are independent of recursion, but the `Cats-Effect` `IO` monad, for instance, executes a `FSM` of fibers via an iterative loop
disguised as a `@tailrec`-annotated method called `runLoop`; nevertheless, if there is an invocation not in the scope of
either `flatMap` or `map` (like a first invocation), it is not stack–safe.

In order to pass through those intermediary steps and analyze those relations, we use as a running example a (variant of a)
puzzle known as the `N Queens Problem`. Given a chess board - a square grid of `NxN` - and `N` queens, with other possible
fixed pieces scattered on the board, to solve the problem recurs to placing them on the free cells of the board, such that
they do not attack each other.

In the case of an empty board, a solution obviously implies that the queens do not share the same row, column, main or
secondary diagonal; but, the board can also be non–empty - containing pieces at various coordinates.

The N-Queens Problem - the "native" algorithm
---------------------------------------------

Following are the types and classes used in the algorithm.

```Scala
case object MaxSolutionsReached extends Throwable

type Coord[T] = (T, T)

extension [T](row: T)
  inline infix def x(col: T): Coord[T] = (row, col)

extension [T](self: Coord[T])
  inline def col: T = self._2
  inline def row: T = self._1

case class Board(N: Int, private[Board] val squares: List[List[Boolean]]):
  def this(squares: List[List[Boolean]]) = this(squares.size, squares)
  require(squares.length == N && squares.forall(_.length == N))
  def apply(i: Int)(j: Int): Boolean = squares(i)(j)

import scala.collection.mutable.Stack

type Point = Coord[Int]
type Solution = List[Point]
type PartialSolution = Stack[Point]

import scala.collection.Seq

class EmptyBoard(n: Int) extends Board(n, List.fill(n)(List.fill(n)(false))):
  inline override def apply(i: Int)(j: Int): Boolean = false
```

A `Board` (possibly empty - the `EmptyBoard` class), has squares whose `Point`-coordinates are pairs of `row` and `col`umn.

The `Validator` object is given for the empty board, for brevity:


```Scala
import scala.util.control.NonLocalReturns.{ returning, throwReturn => thr }

object Validator:

  def apply(solution: Seq[Point])
           (using board: Board): Boolean = returning:
    for
      n <- 0 until board.N
      m <- (n + 1) until board.N
      p = solution(n)
      q = solution(m)
    do
      if false ||
        p.row == q.row ||
        p.col == q.col ||
        p.row - p.col == q.row - q.col ||
        p.row + p.col == q.row + q.col ||
        false
      then
        thr(false)
    true
```

The main method of the "native" algorithm has two implicit parameters: the maximum number of solutions and the `Board`. The
recursive algorithm (`nqueens`) has two parameters: the number `k` of queens left to place, and the (current) point `q` where
to continue placing this rest of the queens.

When the latter reaches the row outside the board, it means there is still at least a queen left to place, but we're out of
coordinates where to place it.

When the former reaches zero, the current solution is validated, and if this succeeds, it is printed. A maximum number of
solutions reached, throws the `MaxSolutionsReached` exception.

Otherwise, if the current column has reached outside the board, the algorithm recurses with the next row and column 0.

If the current point is on the board, there are two recursive calls, without or with a queen placed on the board (at the
current point), the latter only if the current square is empty (always true for empty `Board`s).

```Scala
def queens(using M: Long, board: Board): Unit =
  val currentSolution: PartialSolution = scala.collection.mutable.Stack[Point]()
  var maxSolutions = M
  nqueens(board.N, 0 x 0)
  def nqueens(k: Int, q: Point): Unit =
    if q.row == board.N
    then
      return
    else if k == 0
    then
      if Validator(currentSolution)
      then
        println(currentSolution.sorted)
        maxSolutions -= 1
        if maxSolutions == 0
        then
          throw MaxSolutionsReached
      return
    if q.col == board.N
    then
      nqueens(k, q.row + 1 x 0)
    else
      nqueens(k, q.row x q.col + 1)
      if !board(q.row)(q.col)
      then
        currentSolution.push(q)
        nqueens(k - 1, q.row x q.col + 1)
        currentSolution.pop()
```

An example of invocation of the algorithm is the following:

```Scala
given Board = new EmptyBoard(4)
given Long = 2
try queens catch MaxSolutionsReached => ()
```

All three algorithms solving the N Queens Problem presented hereafter use recursion, meaning they define a function that
contains invocations of itself several times in its body. The “native” approach presented concludes that the particularity to
this kind of programming is that calls to the same function occur from inside the body of the same function. This need not be
strictly so. We urge the reader to think of the case of indirect recursion, such as mutually-recursive functions, for
instance. Even if not all contiguous calls on the stack are to the same function, still the situation is that it is the main
characteristic of the usage of the stack, i.e., that it is _expensive_ - especially for `JVM` languages.

Let us actually introduce an indirect call to `nqueens` through a function `pile_up` and rewrite the three recursive calls of
the `nqueens` function thus:

```Scala
def pile_up(thunk: => Unit): Unit = thunk
def queens(using M: Long, board: Board): Unit =
  val currentSolution: PartialSolution = scala.collection.mutable.Stack[Point]()
  var maxSolutions = M
  nqueens(board.N, 0 x 0)
  def nqueens(k: Int, q: Point): Unit =
    if q.row == board.N
    then
      return
    else if k == 0
    then
      if Validator(currentSolution)
      then
        println(currentSolution.sorted)
        maxSolutions -= 1
        if maxSolutions == 0
        then
          throw MaxSolutionsReached
      return
    if q.col == board.N
    then
      pile_up(nqueens(k, q.row + 1 x 0))
    else
      pile_up(nqueens(k, q.row x q.col + 1))
      if !board(q.row)(q.col)
      then
        currentSolution.push(q)
        pile_up(nqueens(k - 1, q.row x q.col + 1))
        currentSolution.pop()
```

Because the by-name parameter `thunk` occurs unconditioned and exactly once in the body of `pile_up`, the net effect is that
it will be evaluated, which will place a call on the stack, to the same function `nqueens`, but now these calls - since they
are the only ones - will be pairwise intermingled with calls to `pile_up`, still occurring from inside `nqueens`.

Notice two complementary facts resulting from this refactoring:

1. the presence of recursive calls overflowing the stack has not been ameliorated, but
1. each recursive call has been “detached” as a thunk from its hardcoded original form. The notion of closure can prevent (1)
   as it welcomes (2).

[Previous](https://github.com/sjbiaga/kittens/blob/main/covariant-1-contravariant/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/queens-2-heap/README.md)
