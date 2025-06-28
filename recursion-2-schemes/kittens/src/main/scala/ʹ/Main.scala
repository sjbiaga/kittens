package ʹ

import cats.Functor, cats.syntax.functor.*

import ExprF.*
import FacF.*

object Main:

  type ExprFacF[R] = Either[ExprF[R], FacF[R, Long]]

  object ExprFacF:
    implicit val kittensExprFacFunctor: Functor[ExprFacF] =
      new Functor[ExprFacF]:
        override def map[A, B](ea: ExprFacF[A])(f: A => B): ExprFacF[B] =
          ea match
            case Left(xa) => Left(kittensExprFunctor.map(xa)(f))
            case Right(fa) => Right(kittensFacFunctor.map(fa)(f))

    def inL[R](xa: ExprF[R]) = Left(xa)
    def inR[R](fa: FacF[R, Long]) = Right(fa)

  import ExprFacF.*

  def factorial(n: Long): ExprFacF[Long] =
    if n <= 0
    then
      inL(OneF)
    else
      inR(FacF(n-1, n))

  def fibonacci(n: Long): ExprF[Long] =
    if n <= 1
    then
      ValF(1L min (0L max n))
    else
      AddF(n-1, n-2)

  final case class Fix[F[_]](unfix: F[Fix[F]])

  def ana[F[_]: Functor, A](f: A => F[A]): A => Fix[F] =
    a => Fix(f(a) map ana(f))

  def cata[F[_]: Functor, A](f: F[A] => A): Fix[F] => A =
    fix => f(fix.unfix map cata(f))

  extension [F[_], A](alg: F[A] => A)
    infix def :+:[G[_]](algʹ: G[A] => A): Either[F[A], G[A]] => A =
      _.fold(alg, algʹ)

  def main(args: Array[String]): Unit =
    println {
      ana(factorial).apply(5)
    }
    println {
      (ana(factorial) andThen cata(eval :+: evalʹ)).apply(5)
    }
    println {
      ana(fibonacci).apply(5)
    }
    println {
      (ana(fibonacci) andThen cata(eval)).apply(5)
    }
