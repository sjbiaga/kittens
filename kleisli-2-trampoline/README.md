[First](https://github.com/sjbiaga/kittens/blob/main/queens-3-trampoline/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/nat-1-trampoline/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/monoid-1-option/README.md)

Lesson 04: Trampoline and Monads (cont'd)
=========================================

Exercise 04.1
-------------

If a `Functor` were the identity of functors (types with a `map` method), a `Kleisli` would be the study of the `flatMap`
parameter `f: A => F[B]`:

```Scala
package cats
package data

/**
 * Represents a function `A => F[B]`.
 */
final case class Kleisli[F[_], -A, B](run: A => F[B]) ...
```

which is why composition of `Kleisli` objects with `andThen` can replace the composition function `::` of `f: A => F[B]` with
`g: B => F[C]`:

```Scala
object Trampoline:
  extension [A, B](f: A => Trampoline[B])
    inline def ::[C](g: B => Trampoline[C]): A => Trampoline[C] =
      f(_).flatMap(g)
```

Re-implement `Trampoline` with `Kleisli` objects instead of arrows, via composition with the `Kleisli#andThen` method instead
of the left-to-right composition of Kleisli arrows. Give a natural transformation from `Trampoline` to `cats.Eval`.

Solution - Part 1
-----------------

We introduce prior an alias for `Kleisli` `case` `class`es wrapping functions `A => Trampoline[B]`:

```Scala
import cats.data.Kleisli

type Kleisliʹ[A, B] = Kleisli[Trampoline, A, B]
```

The composition with the `Kleisli#andThen` method requires an implicit typeclass instance of the `FlatMap` typeclass for
`Trampoline`; for this, we anonymously instantiate the `StackSafeMonad` trait, implementing `pure` and `flatMap`:

```Scala
import cats.StackSafeMonad

object Trampoline:

  implicit val kittensTrampolineFlatMapInstance: cats.FlatMap[Trampoline] =
    new StackSafeMonad[Trampoline]:
      def pure[A](a: A): Trampoline[A] =
        Trampoline.Done(a)
      def flatMap[A, B](fa: Trampoline[A])(f: A => Trampoline[B]): Trampoline[B] =
        Trampoline.FlatMap(fa, Kleisli(f))
```

Here is `Trampoline` rewritten using `Cats`' `Kleisli` type:

```Scala
import cats.data.Kleisli
import cats.StackSafeMonad

type Kleisliʹ[A, B] = Kleisli[Trampoline, A, B]

enum Trampoline[+A]:
  case Done[+A](value: A) extends Trampoline[A]
  case Call[A](closure: Kleisliʹ[Unit, A]) extends Trampoline[A]
  case FlatMap[A, B](self: Trampoline[A], sequel: Kleisliʹ[A, B]) extends Trampoline[B]

  import Trampoline.*

  final def map[B](fun: A => B): Trampoline[B] =
    this.flatMap(fun andThen pure)

  final def flatMap[B](sequel: A => Trampoline[B]): Trampoline[B] =
    FlatMap(this, Kleisli(sequel))

  @annotation.tailrec
  final def apply(): A = this match
    case Done(value) => value
    case Call(closure) => closure.run(())()
    case FlatMap(Done(value), sequel) => sequel.run(value)()
    case FlatMap(Call(closure), sequel) => (closure andThen sequel).run(())()
    case FlatMap(FlatMap(self, prequel), sequel) => FlatMap(self, prequel andThen sequel)()

object Trampoline:

  implicit val kittensTrampolineFlatMapInstance: cats.FlatMap[Trampoline] =
    new StackSafeMonad[Trampoline]:
      def pure[A](a: A): Trampoline[A] =
        Trampoline.Done(a)
      def flatMap[A, B](fa: Trampoline[A])(f: A => Trampoline[B]): Trampoline[B] =
        fa.flatmap(f)

  def pure[A](a: A): Trampoline[A] = new Done(a)

  object Call:
    def apply[A](thunk: => Trampoline[A]): Trampoline[A] = Call(Kleisli(_ => thunk))
```

Solution - Part 2
-----------------

The only change is in the use of the substitute `g.run` - where `g` binds a `Kleisli` value - instead of the Kleisli arrow.

```Scala
import cats.Eval, cats.~>

val nat: Trampoline ~> Eval =
  new (Trampoline ~> Eval):
    def apply[A](ta: Trampoline[A]): Eval[A] =
      ta match
        case Done(a)       => Eval.now(a)
        case Call(g)       => Eval.defer(apply(g.run(())))
        case FlatMap(s, g) => apply(s).flatMap(g.run andThen apply)
```

[First](https://github.com/sjbiaga/kittens/blob/main/queens-3-trampoline/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/nat-1-trampoline/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/monoid-1-option/README.md)
