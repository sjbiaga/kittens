[Previous](https://github.com/sjbiaga/kittens/blob/main/expr-08-monoidK/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/nat-3-trampoline/README.md)

Lesson 06: Natural Transformations
==================================

We return to this topic started in [Lesson 03 - Natural Transformations: Swapping the Additive with the Multiplicative](https://github.com/sjbiaga/kittens/blob/main/expr-03-swap/README.md).

We already introduced in a previous
[Lesson 04 - `Trampoline` `Monad`](https://github.com/sjbiaga/kittens/blob/main/queens-3-trampoline/README.md) the
implementation of a `Trampoline`, let us recall it here:

```Scala
sealed abstract trait Trampoline[+A]:
  import Trampoline._

  final def map[B](fun: A => B): Trampoline[B] =
    this.flatMap(fun andThen pure)

  final def flatMap[B](sequel: A => Trampoline[B]): Trampoline[B] =
    FlatMap(this, sequel)

  @annotation.tailrec
  final def apply(): A = this match
    case Done(value) => value
    case Call(closure) => closure(())()
    case FlatMap(Done(value), sequel) => sequel(value)()
    case FlatMap(Call(closure), sequel) => (closure :: sequel)(())()
    case FlatMap(FlatMap(self, prequel), sequel) => FlatMap(self, prequel :: sequel)()

object Trampoline:

  extension [A, B](prequel: A => Trampoline[B])
    inline def ::[C](sequel: B => Trampoline[C]): A => Trampoline[C] =
      prequel(_).flatMap(sequel)

  final case class Done[+A](value: A) extends Trampoline[A]

  final case class Call[A](closure: Unit => Trampoline[A]) extends Trampoline[A]

  final case class FlatMap[A, B](self: Trampoline[A], sequel: A => Trampoline[B]) extends Trampoline[B]

  def pure[A](a: A): Trampoline[A] = new Done(a)

  object Call:
    def apply[A](thunk: => Trampoline[A]): Trampoline[A] = Call { _ => thunk }
```

And we could implement a recursive algorithm. This time, let us try `fibonacci`, which returns an `Int`eger rather than
`Unit`:

```Scala
import Trampoline._

def fibonacci(k: Int): Trampoline[Int] =
  if k < 2
  then
    Done(1 min (0 max k))
  else
    for
      m <- Call { fibonacci(k - 2) }
      n <- Call { fibonacci(k - 1) }
    yield
      n + m
```

As it is, `Scala` has its own implementation of a monadic trampoline, in the package `scala.util.control.TailCalls`. The
_natural transformation_ from `Trampoline` to `TailRec` is the following:

```Scala
import cats.arrow.FunctionK, cats.~>
import scala.util.control.TailCalls.{ TailRec, tailcall, done }

val kittensTrampolineToTailRec: Trampoline ~> TailRec =
  new FunctionK[Trampoline, TailRec]:
    def apply[A](ta: Trampoline[A]): TailRec[A] =
      ta match
        case Done(a)       => done(a)
        case Call(g)       => tailcall(apply(g(())))
        case FlatMap(s, g) => apply(s).flatMap(g andThen apply)

kittensTrampolineToTailRec.apply(fibonacci(15)).result
```

Also `Cats` has its own implementation of a trampoline in the `cats.free` package:

```Scala
package cats
package free
type Trampoline[A] = Free[Function0, A]
```

as a `Free` monad, so the _natural transformation_ is the following:

```Scala
import cats.arrow.FunctionK, cats.~>
import cats.free.{ Trampoline => CatsTrampoline, _ }

val kittensTrampolineToCatsTrampoline: Trampoline ~> CatsTrampoline =
  new FunctionK[Trampoline, CatsTrampoline]:
    def apply[A](ta: Trampoline[A]): CatsTrampoline[A] =
      ta match
        case Done(a)       => Free.pure(a)
        case Call(g)       => Free.defer(apply(g(())))
        case FlatMap(s, g) => apply(s).flatMap(g andThen apply)

kittensTrampolineToCatsTrampoline.apply(fibonacci(15)).runTailRec()()
```

Another "monad which controls evaluation" in `Cats` is `Eval`, so the _natural transformation_ is the following:

```Scala
import cats.arrow.FunctionK, cats.~>
import cats.Eval

val kittensTrampolineToCatsEval: Trampoline ~> Eval =
  new FunctionK[Trampoline, Eval]:
    def apply[A](ta: Trampoline[A]): Eval[A] =
      ta match
        case Done(a)       => Eval.now(a)
        case Call(g)       => Eval.defer(apply(g(())))
        case FlatMap(s, g) => apply(s).flatMap(g andThen apply)

kittensTrampolineToCatsEval.apply(fibonacci(15)).value
```

Are these three evaluations of `fibonacci` stack safe? It is true that the implementations of the `apply` methods are
recursive. If we proceed our analysis by cases,

1. `case Done(a)` involves no recursion.

1. `case Call(g)` binds `g` to a closure `Unit => Trampoline[A]`; respectively, `tailcall`, `Free.defer`, and `Eval.defer`
   do all pass the thunk parameter - `apply(g(()))` - `by-name`, and in fact _compile_ it - we know this already - to a
   state of a `FSM`. So not only `fibonacci` had introduced the `FSM` state `Call(g)`, but also, respectively, `tailcall`,
   `Free.defer`, and `Eval.defer` do. When it is the turn of the thunk, `g(())` will return a new state, after which the
   `apply` method will process it next.

1. `case FlatMap(s, g)` transforms the source `s`, and then invokes the `flatMap` method upon, which in all three cases is
   known to compile to a `FlatMap`-like state. `apply` occurs a third time as part of the composition `g andThen apply`, but
   virtually (pattern-matching might not even reach it).

the answer is _twice_ yes: the source `Trampoline` is stack safe anyway, and the target, respectively, `TailRec`,
`CatsTrampoline`, and `Eval`, is anyway too.

Note that there are two `FSM`s involved: the source of the natural transformation, i.e., `Trampoline`, and, the target, i.e.,
respectively, `TailRec`, `CatsTrampoline`, and `Eval`.

[Previous](https://github.com/sjbiaga/kittens/blob/main/expr-08-monoidK/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/nat-3-trampoline/README.md)
