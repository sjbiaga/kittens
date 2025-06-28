package ʹʹ

import cats.Functor
import cats.syntax.functor.*

import ExprF.*

object Main:

  def fibonacci(n: Long): ExprF[Long] =
    if n == 0
    then
      ZeroF
    else if n == 1
    then
      OneF
    else
      AddF(n-1, n-2)

  final case class Fix[F[_]](unfix: F[Fix[F]])

  def ana[F[_]: Functor, A](f: A => F[A]): A => Fix[F] =
    a => Fix(f(a) map ana(f))

  def cata[F[_]: Functor, A](f: F[A] => A): Fix[F] => A =
    fix => f(fix.unfix map cata(f))

  def main(args: Array[String]): Unit =
    println {
      (ana(fibonacci) andThen cata(eval)).apply(5)._2
    }
