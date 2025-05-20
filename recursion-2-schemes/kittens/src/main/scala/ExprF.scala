import cats.{ Applicative, Eval, Functor }

sealed trait ExprF[+R]
case class AddF[+R](lhs: R, rhs: R) extends ExprF[R]
case class SubF[+R](lhs: R, rhs: R) extends ExprF[R]
case object ZeroF extends ExprF[Nothing]
case class MulF[+R](lhs: R, rhs: R) extends ExprF[R]
case class DivF[+R](lhs: R, rhs: R) extends ExprF[R]
case object OneF extends ExprF[Nothing]
case class InvF[+R](rhs: R) extends ExprF[R]
case class ValF[T](n: T) extends ExprF[Nothing]
case class FacF[+R, T](n: R, k: T) extends ExprF[R]

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
           case FacF(n, k)     => FacF(f(n), k)
           case it @ (ValF(_) | ZeroF | OneF) => it

  def eval(xa: ExprF[Long]): Long =
    xa match
      case AddF(lhs, rhs)   => lhs + rhs
      case SubF(lhs, rhs)   => lhs - rhs
      case MulF(lhs, rhs)   => lhs * rhs
      case DivF(lhs, rhs)   => lhs / rhs
      case InvF(rhs)        => 0 - rhs
      case ValF(n: Long)    => n
      case FacF(n, k: Long) => n * k
      case ZeroF            => 0
      case OneF             => 1

  def evalʹ(xa: ExprF[Eval[Long]])(implicit A: Applicative[Eval]): Eval[Long] =
    xa match
      case AddF(lhs, rhs)   => A.map2(lhs, rhs)(_ + _)
      case SubF(lhs, rhs)   => A.map2(lhs, rhs)(_ - _)
      case MulF(lhs, rhs)   => A.map2(lhs, rhs)(_ * _)
      case DivF(lhs, rhs)   => A.map2(lhs, rhs)(_ / _)
      case InvF(rhs)        => A.map(rhs)(0L - _)
      case ValF(n: Long)    => A.pure(n)
      case FacF(n, k: Long) => A.map(n)(_ * k)
      case ZeroF            => A.pure(0L)
      case OneF             => A.pure(1L)
