import cats.{ Eval, Functor }

import ExprF.*

object Mainʹ:

  def factorial(n: Long): ExprF[Long] =
    if n <= 0
    then
      OneF
    else
      FacF(n-1, n)

  def fibonacci(n: Long): ExprF[Long] =
    if n == 0
    then
      ZeroF
    else if n == 1
    then
      OneF
    else
      AddF(n-1, n-2)

  final case class Fix[F[_]](unfix: F[Eval[Fix[F]]])

  def ana[F[_]: Functor, A](f: A => F[A]): A => Eval[Fix[F]] =
    anaEval(f andThen Eval.later)
  def anaEval[F[_], A](f: A => Eval[F[A]])(implicit F: Functor[F]): A => Eval[Fix[F]] =
    f(_).map(F.lift(anaEval(f)) andThen Fix.apply)

  // def cata[F[_], A](f: F[Eval[A]] => Eval[A])(implicit F: Functor[F]): Eval[Fix[F]] => Eval[A] =
  //   _.flatMap(fix => f(F.map(fix.unfix)(cata(f))))

  def cata[F[_], A](f: F[Eval[A]] => Eval[A])(implicit F: Functor[F]): Eval[Fix[F]] => Eval[A] =
    _.flatMap(((_: Fix[F]).unfix) andThen F.lift(cata(f)) andThen f)

  def main(args: Array[String]): Unit =
    println {
      (ana(factorial) andThen cata(evalʹ))(5L).value
    }
