[First](https://github.com/sjbiaga/kittens/blob/main/queens-1-native/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/queens-1-native/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-01-trait/README.md)

Lesson 02: Closures and Stack Safety (cont'd)
=============================================

Let us make a first small step towards stack safety, then a “jump” through a “`Trampoline`”, until the giant leap to monads.

Closures
--------

What is a closure? A _closure_ is a function object that captures free variables, and is said to be “closed” over the
variables visible at the time it is created. The notion is related to Java `SAM` or `@FunctionalInterface`-annotated
interfaces; in fact, in Java, a _lambda_ is an object, instance of an anonymous class that implements a `SAM` interface.

But a closure is more involved, able to capture variables that are not final, thus being functional programming specific. And
let us just say from the onset that the alternative to the stack is the _heap_. There would have been probably no use for
creating closures, had it not been for the possibility of placing them elsewhere than piling them up on the stack.

Heap
----

In Scala, a pattern for implementing a finite state machine (`FSM`) is by defining a `sealed trait` - with some `final`
method - and deriving from it a few `case object`s/`case class`es, i.e., a _closed hierarchy_: then, the method is defined by
pattern-matching on the `case object`s/`case class`es - each case being a state. So is the case with the `Heap` type from the
following code. It is introduced with the purpose of switching from stack to heap in a rather primitive manner.

```Scala
sealed abstract trait Heap:
  protected def apply(): Option[Heap]
  @annotation.tailrec
  final def call: Unit =
    this() match
      case Some(heap) => heap.call                                   // line #06
      case _ =>

object Heap:
  case object Done extends Heap:
    override protected def apply(): Option[Heap] = None

  final case class Call(closure: Unit => Heap) extends Heap:
    override protected def apply(): Option[Heap] = Some(closure(())) // line #14

  object Call:
    inline def apply(thunk: => Heap): Call = new Call(_ => thunk)

  final case class More(calls: Heap*) extends Heap:                  // line #19
    override protected def apply(): Option[Heap] = calls
      .headOption
      .map {
        _() match
          case Some(it: More) => More((it.calls ++ calls.tail)*)     // line #24
          case Some(it: Call) => More((it +: calls.tail)*)           // line #25
          case _ => More(calls.tail*)
      }
```

The final method `call` is annotated with `@tailrec` annotation: had the method not been `final`, the Scala compiler would
have issued an error: `TailRec optimisation not applicable, method call is neither private nor final so can be overridden.`

A parameterless `final` method `call` is used to invoke the closures in the heap, regardless of the subtype extending
`Heap`. Another `protected` method is `apply` with the return type `Option[Heap]`. There is one `case object` `Done` that
does not reserve any heap: it marks the end of recursion. Then, just a single recursive call captured as a closure is handled
with the `Call` `case class`, of just one parameter - the closure. Notice that all closures have as return type the base
`sealed trait` `Heap`.

There are two more issues that need to be settled:

1. as the heap must behave in a stack-like manner, how can the more recent closures be prepended to those earlier, and
1. how can a sequence of consecutive closures be _not_ modeled with a single `Call` - which would not only be confusing, but
   wrong, since the closures being just values, solely the last one will be retained.

The N Queens Problem - the "heap" algorithm
-------------------------------------------

But prior to that, let us implement the `queens` method using `Heap` and (only) closures, as follows:

```Scala
def queens(using M: Long, board: Board): Unit =
  var maxSolutions = M
  Call { hqueens(board.N, 0 x 0)(Nil) }.call
  def hqueens(k: Int, q: Point)(implicit currentSolution: Solution): Heap =
    if q.row == board.N
    then
      Done
    else if k == 0
    then
      if Validator(currentSolution)
      then
        println(currentSolution.sorted)
        maxSolutions -= 1
        if maxSolutions == 0
        then
          throw MaxSolutionsReached
      Done
    else if q.col == board.N
    then
      Call { hqueens(k, q.row + 1 x 0) }                                   // line #a
    else
      More (                                                               // line #b
        Call { hqueens(k, q.row x q.col + 1) }                             // line #c
      , if !board(q.row)(q.col)
        then
          Call { hqueens(k - 1, q.row x q.col + 1)(currentSolution :+ q) } // line #d
        else
          Done                                                             // line #e
      )
```

A closer look at the `def`inition of `hqueens` shows that the return type of this function is `Heap` - a type defined in the
previous listing. So in this approach to the N Queens Problem, based on closures, instead of piling up a recursive call on
the stack, there is rather a small amount of heap that is returned and which contains the necessary calls to `hqueens`, if
any, as one or more closures.

This shift (towards the heap) of memory usage paradigm (other than the stack) is _stack safety_.

Let us analyze from where the initial invocation to `hqueens` occurs:

```Scala
Call { hqueens(board.N, 0 x 0)(Nil) }.call
```

The expression inside the braces is the closure/thunk, and it is just a value, it does nothing besides becoming the parameter
to the `Call` `case class`. At the moment the `call` method is invoked for a receiver of type `Call`, the closure is
evaluated in line #14. This implies a call to `hqueens` which will likely pass through lines #b-#e. There are two closures
that must be returned, so answering (2), these must be _sequenced_. Hence the need for the `More` `case class` in line #19:
upon pattern-matching as the `heap` variable in line #06, the second invocation of the `call` method will have a receiver of
type `More`.

Now, because the head element in the sequence is likely to be a `Call` object, a second pass through lines #b-#e will return
an object of type `More`. So answering (1), in line #24, the more recent calls (`it.calls`) are prepended to the earlier
calls (`calls.tail`), yielding `More((it.calls ++ calls.tail)*)`. In this manner there is always a single instance of `More`
because care is taken to flatten the closures in a stack-like sequence.

Of course, when a row is done and line #a is reached, then line #25 will pattern-match. Thus, an instance of `Call` is
“pushed on” the heap. Otherwise, the `FSM` will continue with the tail of the heap, until there are no more closures, which
signifies the end of the algorithm.

[First](https://github.com/sjbiaga/kittens/blob/main/queens-1-native/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/queens-1-native/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-01-trait/README.md)
