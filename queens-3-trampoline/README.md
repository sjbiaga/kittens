Lesson 04: Trampoline and Monads
================================

The code in this lesson makes the passage from closures to monads and is _originally_ adapted from section
"6 Free Monads: A Generalization of Trampoline" in the article
[Stackless Scala With Free Monads](https://days2012.scala-lang.org/sites/days2012/files/bjarnason_trampolines.pdf) by
Rúnar Óli Bjarnason; the `resume` method therein has been originally rewritten as `apply`, which we hope is much more clearer
to the reader.

In [Lesson 02 - Heap](https://github.com/sjbiaga/kittens/blob/main/queens-2-heap/README.md) it is mentioned that trading
stack for heap was done in a “primitive manner”. Let us see now a more advanced style of programming in Scala, using types
with `map` and `flatMap` methods - a tiny language. Another basic observation is that `Heap` worked only for functions
returning `Unit`: so let us relax this condition.

Thus, in general, if we had a `method` of type `Trampoline[T]` with several consecutive calls

```Scala
def method(arg1, arg2, ...): Trampoline[T] =
  val res1 = Call { () => <closure1> }()
  val res2 = Call { () => <closure2> }()
  ...
  val resN = Call { () => <closureN> }()
  Done { combine(resK*) }
```

(here we anticipate the `Trampoline[T]` type - all we need to know at this point is that it has a method of type `T`):

```Scala
sealed abstract trait Trampoline[+T]:
  final def apply(): T = this match
    case Call(closure) => closure()()
    ...
  ...
```

the obvious error that we make is that retrieving the results of each closure using the `apply()` method of the trampoline,
will place the calls to `method` on the stack, so we’re back where we started. If we want to keep the closure as a (first)
parameter to `Call`, what is needed is to separate the usage of the result; we do not want to use the result immediately,
quite the opposite, we want to use the result when we want it (especially not from inside the body of `method`),
so we intend to add a block as a second parameter to `Call`, thus _delaying_ and relaying the use to the function.

```Scala
// A failed intent to reach stack safety

case class Call[T](closure: () => Trampoline[T], block: T => Trampoline[T]) extends Trampoline[T]

sealed abstract trait Trampoline[+T]:
  def resume: Trampoline[T] Either T = this match
    case Call(closure, block) =>
      Left(block(closure()()))
    case Done(result) =>
      Right(result)
  final def apply(): T
    var res = this.resume
    while res.isLeft
    do
      res = res.left.get.resume
    res.right.get

def method(arg1, arg2, ...): Trampoline[T] =
  Call ({ () => <closure1> }, { res1 =>
    Call ({ () => <closure2> }, { res2 =>
      ...
      Call ({ () => <closureN> }, { resN =>
        Done { combine(resK*) }
      })
      ...
    })
  })
```

Note how these blocks are _nested_ in `method` and have _the same_ return type. We also added a `resume` method to the
`Trampoline` trait, that obtains the result from the closure and applies it the block, yielding an unevaluated
`Trampoline`. This is _partially_ what we wanted (`method` is invoked from outside its body, i.e., from `resume` - so the
calls to `method` are stack–safe), as this solution is still not yet satisfactory: through
line `Left(block(closure()()))` - where the second pair of parentheses invokes it -, the final method ”`apply(): T`“ becomes
_indirectly_ recursive, hence not stack–safe, resulting in the failure of the whole construction.

If the two methods ”`resume`“ and “`apply`“ in the base `trait` `Trampoline` represent the _execution_ of a `FSM`, then the
body of `method` composed of instances of `case class`es surely represents the _compilation_ of the program into states of the
`FSM` - “pulled” upon invocation.

Of course, the Scala compiler cannot “detect” such `case class`es with two parameters. Nevertheless, it can actually apply a
“desugared” translation scheme that uses blocks, but requires `Trampoline` to have a method named `flatMap` that is
parameterized with a “`block: A => Trampoline[B]`”,

```Scala
sealed abstract trait Trampoline[+A]:
  def flatMap[B](block: A => Trampoline[B]): Trampoline[B] = ???
object Trampoline:
  case class Call[A](closure: () => Trampoline[A]) extends Trampoline[A]
```

leaving the association between the closure and the block to the implementation of `flatMap`.

```Scala
// The proper mode to achieve stack safety

def method(arg1, arg2, ...): Trampoline[T] = // translation
  Call { () => <closure1> }.flatMap { res1 =>
    Call { () => <closure2> }.flatMap { res2 =>
      ...
      Call { () => <closureN> }.flatMap { resN =>
        Done { combine(resK*) }
      }
      ...
    }
}
```

What `flatMap` does here is that it indroduces a _delay_ between the capture of the closure and its use: _compiling_, in
other words.

Scala also provides a much more readable syntactic sugar known as a `for`–comprehension.

```Scala
// The proper mode to achieve stack safety

def method(arg1, arg2, ...): Trampoline[T] = // for-comprehension
   for
     res1 <- Call { () => <closure1> }
     res2 <- Call { () => <closure2> }
     ...
     resN <- Call { () => <closureN> }
   yield
     combine(resK*)
```

The simplest way to _associate_ a closure of a `Call` with a `flatMap` block is trough a mediating definition:

```Scala
def flatMap[B](block: A => Trampoline[B]): Trampoline[B] = FlatMap(this, block)
```

which - at the most basic level - _compiles_ the invocation of `flatMap` upon a receiver of type `Trampoline` to an
intermediary state (heap), where the definition of `FlatMap` from the companion object is:

```Scala
object Trampoline:
  case class FlatMap[A, B](self: Trampoline[A], sequel: A => Trampoline[B]) extends Trampoline[B]
```

Again, those blocks from within `method` are nested and they all have the same return type (`Trampoline[T]`), even though
`flatMap` is parameterized with a generic type `B`. In plain Scala terms, `Trampoline` is a _monad_ because it contains also
a method `map` defined in terms of `flatMap`:

```Scala
final def map[B](fun: A => B): Trampoline[B] = this.flatMap(fun andThen pure)
```

`Trampoline` `Monad`
--------------------

So the final code for the `Trampoline` is given below. In the `apply` method, "`closure :: sequel`" and "`prequel :: sequel`"
are compositions of two functions via `flatMap`. This extension method (`::`) is defined in the companion object. The line
`prequel(_).flatMap(sequel)` is an anonymous function, standing for `{ a => prequel(a).flatMap(sequel) }`: if passed the
argument `a`, it obtains a `Trampoline` and with it as the receiver it compiles into the state `FlatMap(prequel(a), sequel)`.

```Scala
enum Trampoline[+A]:
  case Done[+A](value: A) extends Trampoline[A]
  case Call[A](closure: Unit => Trampoline[A]) extends Trampoline[A]
  case FlatMap[A, B](self: Trampoline[A], sequel: A => Trampoline[B]) extends Trampoline[B]

  import Trampoline._

  final def map[B](fun: A => B): Trampoline[B] =
    this.flatMap(fun andThen pure)

  final def flatMap[B](sequel: A => Trampoline[B]): Trampoline[B] =
    FlatMap(this, sequel)

  @annotation.tailrec
  final def apply(): A = this match
    case Done(value) => value                                                          // line #a
    case Call(closure) => closure(())()                                                // line #b
    case FlatMap(Done(value), sequel) => sequel(value)()                               // line #c
    case FlatMap(Call(closure), sequel) => (closure :: sequel)(())()                   // line #d
    case FlatMap(FlatMap(self, prequel), sequel) => FlatMap(self, prequel :: sequel)() // line #e

object Trampoline:

  extension [A, B](prequel: A => Trampoline[B])
    inline def ::[C](sequel: B => Trampoline[C]): A => Trampoline[C] =
      prequel(_).flatMap(sequel)

  def pure[A](a: A): Trampoline[A] = new Done(a)

  object Call:
    inline def apply[A](closure: => Trampoline[A]): Trampoline[A] = new Call(_ => closure)
```

[In the literature, `::` is known as _left-to-right composition of Kleisli arrows_. [Exercise 04.1](https://github.com/sjbiaga/kittens/blob/main/kleisli-2-trampoline/README.md) shows how `Kleisli` arrow types can be used instead.]

Let us analyze line #e, which we can rewrite as:

```Scala
case FlatMap(outer @ FlatMap(inner, prequel), sequel) => FlatMap(inner, prequel :: sequel)()
```

We know that `FlatMap` states result straight from calls to `flatMap`; hence, reverse engineering the pattern-matching in
line #e, this resulted from `outer.flatMap(sequel)`; but, given that `outer` is `FlatMap(inner, prequel)`, line #e further
resulted from

```Scala
inner.flatMap(prequel).flatMap(sequel)
```

Thus, going the other way around, the pattern-matching transforms into

```Scala
FlatMap(inner, prequel :: sequel)
```

which is another saying for

```Scala
inner.flatMap(prequel :: sequel)
```

So, we passed from `inner.flatMap(prequel).flatMap(sequel)` to `inner.flatMap(prequel :: sequel)`, or from two consecutive
`flatMap`s to just one: in this way, our programs' evaluation reduces towards results. But how did we obtain the former in
the first place? Definitely _not_ from a translation of a `for`-comprehension! Can you guess why? It is because the
`flatMap`s in `for`-comprehensions are _nested_:

```Scala
for
  x <- outer
  y <- inner
yield
  ...
```

translates to:

```Scala
outer.flatMap { x =>
  inner.flatMap { y =>
    ...
  }
}
```

which results in `FlatMap(outer, { x => FlatMap(inner { y => ... }) })`. This definitely does not pattern-match in line #e!
Yet, this does not stop somebody from writing:

```Scala
Done(())
  .flatMap(f)
  .flatMap(g)
  .flatMap(h)
  ...
```

only it is a different style (often with the `Future` monad) of programming than `for`-comprehensions.

The N Queens Problem - the "trampoline" algorithm
-------------------------------------------------

For the N Queens Problem we present an implementation using `Trampoline`, after which follows a commentary for an example of
the execution of the `FSM`.

```Scala
def queens(using M: Long, board: Board): Unit =
  var maxSolutions = M
  tqueens(board.N, 0 x 0)(Nil)()
  def tqueens(k: Int, q: Point)(implicit currentSolution: Solution): Trampoline[Unit] =
    if q.row == board.N
    then
      Done(())
    else if k == 0
    then
      if Validator(currentSolution)
      then
        println(currentSolution.sorted)
        maxSolutions -= 1
        if maxSolutions == 0
        then
          throw MaxSolutionsReached
      Done(())
    else if q.col == board.N
    then
      Call { tqueens(k, q.row + 1 x 0) }                            // line #20
    else
      for
        _ <- Call { tqueens(k, q.row x q.col + 1) }                 // line #23
        _ <- Call {                                                 // line #24
          if !board(q.row)(q.col)
          then
            tqueens(k - 1, q.row x q.col + 1)(currentSolution :+ q) // line #27
          else
            Done(())                                                // line #29
        }
      yield
        ()
```

Let us focus on lines #20 and #23-#29, the latter which - via the Scala translation scheme of the `for`-comprehension -, are
compiled one after the other:

```Scala
Call { _ => tqueens(k, q.row x q.col + 1) }
.flatMap { _ =>
  Call { _ => if !board(q.row)(q.col) then tqueens(k-1, q.row x q.col + 1)(currentSolution :+ q)
              else Done(()) }
  .map { _ => () }
}
```

There are no recursive invocations! So let us compile this program into a state of the `FSM` (note that the `if-then-else` in
the block cannot be yet evaluated because it occurs in a function body not yet applied the argument to):

```Scala
FlatMap(Call { _ => tqueens(k, q.row x q.col + 1) }, { _ =>
  Call { _ => if !board(q.row)(q.col) then tqueens(k-1, q.row x q.col + 1)(currentSolution :+ q)
              else Done(())
       }.map { _ => () }
})
```

Now, resuming - by line #d -, then assuming - for the sake of simplicity - that the closure returns `Done(())`, and compiling
again, we obtain:

```Scala
FlatMap(Done(()), { _ =>
  Call { _ => if !board(q.row)(q.col) then tqueens(k-1, q.row x q.col + 1)(currentSolution :+ q)
              else Done(())
       }.map { _ => () }
})
```

which in turn - by line #c - reduces to:

```Scala
Call { _ => if !board(q.row)(q.col) then tqueens(k-1, q.row x q.col + 1)(currentSolution :+ q)
            else Done(())
     }.map { _ => () }
```

which further compiles to:

```Scala
FlatMap(
  Call { _ => if !board(q.row)(q.col) then tqueens(k-1, q.row x q.col + 1)(currentSolution :+ q)
              else Done(()) }
, { _ => () } andThen pure
)
```

which in turn - by line #d and by assuming `board(q.row)(q.col)` be true - reduces to:

```Scala
Done(()).flatMap({ _ => () } andThen pure)
```

which further compiles to `FlatMap(Done(()), { _ => () } andThen pure)` which finally - by line #c - reduces to `Done(())`
and - by line #a - to `()`.

[Previous](https://github.com/sjbiaga/kittens/blob/main/expr-09-ring/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/nat-1-trampoline/README.md)
