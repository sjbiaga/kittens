Lesson 06: Natural Transformations (cont'd)
===========================================

We have seen that for the three equivalent trampolines, there were three natural transformations given. We could have written
the `fibonacci` method thrice instead. However, suppose we had a `class` of `Algorithms`:

```Scala
import Trampoline._

case class Algorithms(n: Int):
  private def fibonacci(k: Int): Trampoline[Int] =
    if k < 2
    then
      Done(1 min (0 max k))
    else
      for
        m <- Call { fibonacci(k - 2) }
        n <- Call { fibonacci(k - 1) }
      yield
        n + m
  private def factorial(k: Int): Trampoline[Int] =
    if k < 1
    then
      Done(1)
    else
      for
        n <- Call { factorial(k - 1) }
      yield
        k * n
  def fib: Trampoline[Int] = fibonacci(n)
  def fac: Trampoline[Int] = factorial(n)

val a = Algorithms(5)
```

There is some benefit still, because we can use the same transformation twice. But could we have a single implementation of
a natural transformation that would work with _all_ (three) _monads_, respectively, `TailRec`, `CatsTrampoline`, and `Eval`?

Taking after [doobie](https://github.com/typelevel/doobie), we could implement a _visitor_ design pattern:

```Scala
import cats.~>

sealed abstract trait Trampoline[A]:
  import Trampoline._

  def visit[F[_]](v: Visitor[F]): F[A] // line #06

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

  trait Visitor[F[_]] extends (Trampoline ~> F):
    final override def apply[A](ta: Trampoline[A]): F[A] = ta.visit(this) // line #25

    def done[A](value: A): F[A]
    final def call[A](closure: Unit => Trampoline[A]): F[A] = fMap(Done(()), closure)
    def fMap[A, B](self: Trampoline[A], cont: A => Trampoline[B]): F[B]

  extension [A, B](prequel: A => Trampoline[B])
    inline def ::[C](sequel: B => Trampoline[C]): A => Trampoline[C] =
      prequel(_).flatMap(sequel)

  final case class Done[A](value: A) extends Trampoline[A]:
    override def visit[F[_]](v: Visitor[F]): F[A] = v.done(value)

  final case class Call[A](closure: Unit => Trampoline[A]) extends Trampoline[A]:
    override def visit[F[_]](v: Visitor[F]): F[A] = v.call(closure) // line #39

  final case class FlatMap[A, B](self: Trampoline[A], sequel: A => Trampoline[B]) extends Trampoline[B]:
    override def visit[F[_]](v: Visitor[F]): F[B] = v.fMap(self, sequel)

  def pure[A](a: A): Trampoline[A] = new Done(a)
```

where

1. the `Visitor` trait extends `Trampoline ~> F` (alias for `cats.arrow.FunctionK` or _natural transformations_)

1. the `Visitor` methods are in one-to-one correspondence with the `FSM` implemented for `Trampoline[A]` using the three
   `case class`es: `Done`, `Call`, and `FlatMap` - a "low-level" language.

1. the `Visitor`s `call` method though delegates to another (`fMap`).

The first time we invoke the algorithm with `apply(a.fib)`, the method `visit` from line #06 will be called in line #25 with
_receiver_ the result from `a.fib` - either `Done`, or `Call`, or `FlatMap`.

The parameter(s) of one of this `case class`es, or parameter(s) of a `FSM` state, will be passed back to the visitor in one
of the corresponding methods `done`, `call`, or `fMap` - a "high-level" language.

The target monad will _translate_ the latter into its tiny language made of `pure` and `flatMap`: this _interpreter_ extends
the `Visitor` trait and can be turned into a singleton nested object:

```Scala
import cats.Monad

class MonadInterpreter[M[_]](implicit val M: Monad[M]):
  object TrampolineInterpreter extends Trampoline.Visitor[M]:
    def done[A](value: A): M[A] = M.pure(value)                           // line #a
    def fMap[A, B](self: Trampoline[A], cont: A => Trampoline[B]): M[B] =
      M.flatMap(apply(self))(cont andThen apply)                          // line #b
```

If the pure "`value`" results from line #a alone, then the algorithm is thus ended. However, `apply(self)` from line #b is
likely to happen more often: in the latter case, `M.flatMap` _delays_ - regardless of the monad type - by _compilation_ to
`M` monad's "low-level" language. Assume we were called from line #39; then, for `Call`s, `self` is `Done(())`, so `apply`
will recurse exactly _once_ from #b to #a (and then jump back).

It is important that `apply` is _not_ recursive, for otherwise we could not guarantee stack safety.

There is another invocation of `apply` in line #b, composed with the `cont`inuation function-parameter, but this is virtual.

Next Scala `REPL` session shows how the same interpreter can be used with various monads, include `Id`.

```Scala
import cats.Eval
implicitly[Monad[Eval]]
MonadInterpreter[Eval].TrampolineInterpreter.apply(a.fib).value

import scala.util.control.TailCalls.TailRec
import cats.instances.tailRec._
implicitly[Monad[TailRec]]
MonadInterpreter[TailRec].TrampolineInterpreter.apply(a.fib).result

import cats.effect.unsafe.implicits.global, cats.effect.IO
implicitly[Monad[IO]]
MonadInterpreter[IO].TrampolineInterpreter.apply(a.fac).unsafeRunSync()

import cats.free.{ Trampoline => CatsTrampoline }
implicitly[Monad[CatsTrampoline]]
MonadInterpreter[CatsTrampoline].TrampolineInterpreter.apply(a.fac).runTailRec()()

import cats.Id
implicitly[Monad[Id]] eq catsInstancesForId == true
MonadInterpreter[Id].TrampolineInterpreter.apply(a.fib)
```

In this last case, the return value of `apply` is also the direct result, while `fMap` instead of compiling, it invokes
`M.flatMap` which is encoded as direct function application - hence, this translation is not stack safe.

It is even possible to translate into _the same_ language, by giving a typeclass instance of `Monad` for `Trampoline`:

```Scala
import cats.StackSafeMonad

implicit val kittensTrampolineMonadInstance: Monad[Trampoline] =
  new StackSafeMonad[Trampoline]:
    //override def ap[A, B](ff: Trampoline[A => B])(fa: Trampoline[A]): Trampoline[B] =
    //  flatMap(ff)(map(fa)(_))
    //override def flatten[A](ffa: Trampoline[Trampoline[A]]): Trampoline[A] =
    //  flatMap(ffa)(identity)
    override def flatMap[A, B](fa: Trampoline[A])(fun: A => Trampoline[B]): Trampoline[B] =
      fa.flatMap(fun)
    //override def map[A, B](fa: Trampoline[A])(fun: A => B): Trampoline[B] =
    //  fa.map(fun)
    override def pure[A](a: A): Trampoline[A] = Trampoline.pure(a)

MonadInterpreter[Trampoline].TrampolineInterpreter.apply(a.fac)()
```

[Previous](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/queens-4-interpreter/README.md)
