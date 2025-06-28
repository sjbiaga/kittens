[First](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/queens-4-interpreter/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/nat-4-list/README.md)

Lesson 06: Natural Transformations (cont'd)
===========================================

We have seen that for the three equivalent trampolines, there were three natural transformations given. We could have written
the `fibonacci` method thrice instead. However, suppose we had a `class` of `Algorithms`:

```Scala
import Trampoline.*

case class Algorithms(n: Int):
  private def fibonacci(k: Int): Trampoline[Int] = ???
  private def factorial(k: Int): Trampoline[Int] = ???
  def fib: Trampoline[Int] = ... fibonacci(n) ...
  def fac: Trampoline[Int] = ... factorial(n) ...
```

There is some benefit still, because we can use the same transformation twice. But could we have a single implementation of
a natural transformation that would work with _all_ (three) _monads_, respectively, `TailRec`, `CatsTrampoline`, and `Eval`,
or, perhaps, more?

Taking after [doobie](https://github.com/typelevel/doobie), we could implement a _visitor_ design pattern:

```Scala
import cats.~>

sealed abstract trait Trampoline[A]:
  import Trampoline.*

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

1. the parameter(s) of one of this `case class`es, or parameter(s) of a `FSM` state, will be passed back to the visitor in
   one of the corresponding methods `done`, `call`, or `fMap` - a "high-level" language.

1. the `Visitor`'s `call` method though delegates to another (`fMap`).

---

It is possible to translate into _the same_ language, by giving typeclass instances of the `Monad` and `Defer` typeclasses
for `Trampoline`:

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

implicit val kittensTrampolineDeferInstance: Defer[Trampoline] =
  new Defer[Trampoline]:
    override def defer[A](fa: => Trampoline[A]): Trampoline[A] = Trampoline.Call(fa)
```

So, let us suppose now we had a `class` of `Algorithms`:

```Scala
import Trampoline.*

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
  private def rec(n: Int): Trampoline[Int] =
    if n == 0 then Done(0)
    else rec(n-1).flatMap(rec)
  def fib: Trampoline[Int] = kittensTrampolineDeferInstance.defer(fibonacci(n))
  def fac: Trampoline[Int] = kittensTrampolineDeferInstance.defer(factorial(n))
  def rec: Trampoline[Int] = kittensTrampolineDeferInstance.defer(rec(n))

val a = Algorithms(25000)
```

Note that - for stack safety - we _must_ wrap the _top_ invocations in `defer`: otherwise, the top calls could overflow the
stack.

---

The first time we invoke the algorithm with `apply(a.rec)`, the method `visit` from line #06 will be called in line #25 with
_receiver_ the result from `a.rec` - because of wrapping inside `kittensTrampolineDeferInstance.defer`, a `FlatMap`.

The target monad will _translate_ the latter into its tiny language made of `pure` and `flatMap`: this _interpreter_ extends
the `Visitor` trait and can be turned into a singleton nested object:

```Scala
import cats.{ Defer, Monad }

class MonadInterpreter[M[_]](implicit M: Monad[M], D: Defer[M]):
  object TrampolineInterpreter extends Trampoline.Visitor[M]:
    def done[A](value: A): M[A] = M.pure(value)                           // line #a
    def fMap[A, B](self: Trampoline[A], cont: A => Trampoline[B]): M[B] =
      M.flatMap(D.defer(apply(self)))(cont andThen apply)                 // line #b
```

If the pure "`value`" results from line #a alone, then the algorithm is thus ended. However, `apply(self)` from line #b is
likely to happen more often: in the latter case, `M.flatMap` _delays_ - regardless of the monad type - by _compilation_ to
`M` monad's "low-level" language. Assume we were called from line #39; then, for `Call`s, `self` is `Done(())`, so `apply`
will recurse exactly _once_ from #b to #a (and then jump back).

Nevertheless, it is important that `apply` were _not_ recursive, for otherwise we could not guarantee stack safety. For this
reason, we require an implicit `Defer[M]` typeclass instance be in scope, so that we also _defer_ `apply(self)` calls in
line #b (by wrapping inside `D.defer`, [which](https://github.com/sjbiaga/kittens/blob/main/recursion-4-Defer/README.md) has
a `call-by-name` parameter of the same type as its result): except `Id`, all the monads presented further below have typeclass
instances of the `Defer` typeclass, and we have given one for `Trampoline`.

There is another invocation of `apply` in line #b, composed with the `cont`inuation function-parameter, but this is _delayed_
(pattern-matching might not even reach it).

Next Scala `REPL` session shows how the same interpreter can be used with various monads, excluding `Id`.

```Scala
MonadInterpreter[Trampoline].TrampolineInterpreter.apply(a.rec)()

import cats.Eval
implicitly[Monad[Eval]]
MonadInterpreter[Eval].TrampolineInterpreter.apply(a.rec).value

import scala.util.control.TailCalls.TailRec
import cats.instances.tailRec.*
implicitly[Monad[TailRec]]
MonadInterpreter[TailRec].TrampolineInterpreter.apply(a.rec).result

import cats.effect.unsafe.implicits.global, cats.effect.IO
implicitly[Monad[IO]]
MonadInterpreter[IO].TrampolineInterpreter.apply(a.rec).unsafeRunSync()

import cats.free.{ Trampoline => CatsTrampoline }
implicitly[Monad[CatsTrampoline]]
MonadInterpreter[CatsTrampoline].TrampolineInterpreter.apply(a.rec).runTailRec()()

import cats.Id
implicitly[Monad[Id]] eq catsInstancesForId == true
MonadInterpreter[Id].TrampolineInterpreter.apply(a.rec) // no Defer[Id] instance!
```

In this last case - were we to ignore wrapping inside `D.defer` and the lack of `Defer[Id]` typeclass instance -, the return
value of `apply` would also be the direct result, while `fMap` instead of compiling, would invoke `M.flatMap` which is encoded
as direct function application - hence, this translation is _not stack safe_ (which is why there is no `Defer[Id`] typeclass
instance in the first place).

[First](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/queens-4-interpreter/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/nat-4-list/README.md)
