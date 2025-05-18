package ʹ

import cats.Functor

sealed trait ExprF[+R]
case class AddF[+R](lhs: R, rhs: R) extends ExprF[R]
case class SubF[+R](lhs: R, rhs: R) extends ExprF[R]
case object ZeroF extends ExprF[Nothing]
case class MulF[+R](lhs: R, rhs: R) extends ExprF[R]
case class DivF[+R](lhs: R, rhs: R) extends ExprF[R]
case object OneF extends ExprF[Nothing]
case class InvF[+R](rhs: R) extends ExprF[R]
case class ValF[T](n: T) extends ExprF[Nothing]

object ExprF:
  implicit val kittensExprFunctor: Functor[ExprF] =
     new Functor[ExprF]:
       override def map[A, B](xa: ExprF[A])(f: A => B): ExprF[B] =
         xa match
           case AddF(lhs, rhs) => AddF(f(lhs), f(rhs))
           case SubF(lhs, rhs) => SubF(f(lhs), f(rhs))
           case MulF(lhs, rhs) => MulF(f(lhs), f(rhs))
           case DivF(lhs, rhs) => DivF(f(lhs), f(rhs))
           case InvF(rhs)      => InvF(f(rhs))
           case it @ (ValF(_) | ZeroF | OneF) => it

  def eval(xa: ExprF[Long]): Long =
    xa match
      case AddF(lhs, rhs)   => lhs + rhs
      case SubF(lhs, rhs)   => lhs - rhs
      case MulF(lhs, rhs)   => lhs * rhs
      case DivF(lhs, rhs)   => lhs / rhs
      case InvF(rhs)        => 0 - rhs
      case ValF(n: Long)    => n
      case ZeroF            => 0
      case OneF             => 1
