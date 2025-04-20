package kittens

import scala.annotation.tailrec

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
    case Done(value) =>
      value
    case Call(closure) =>
      closure(())()
    case FlatMap(Done(value), sequel) =>
      sequel(value)()
    case FlatMap(Call(closure), sequel) =>
      (closure :: sequel)(())()
    case FlatMap(FlatMap(self, prequel), sequel) =>
      FlatMap(self, prequel :: sequel)()

    override def toString(): String =
      @tailrec
      def count(self: Trampoline[?], result: Int): Int =
        self match
          case FlatMap(self, _) => count(self, 1 + result)
          case _                => result
      this match
        case Done(value) => s"Done($value)"
        case Call(closure) => s"Call($closure)"
        case FlatMap(self, sequel) => s"${count(this, 0)}FlatMap($self,$sequel)"

object Trampoline:

  // Kleisli composition
  extension [A, B](prequel: A => Trampoline[B])
    inline def ::[C](sequel: B => Trampoline[C]): A => Trampoline[C] =
      prequel(_).flatMap(sequel)

  def pure[A](a: A): Trampoline[A] = new Done(a)

  object Call:
    inline def apply[A](closure: => Trampoline[A]): Trampoline[A] = new Call(_ => closure)

  import cats.Applicative

  trait Applicativeʹ[F[_]] extends Applicative[F]:
    def map2Trampoline[A, B, Z](fa: F[A], lb: Trampoline[F[B]])(f: (A, B) => Z): Trampoline[F[Z]] =
      lb.map(map2(fa, _)(f))
  