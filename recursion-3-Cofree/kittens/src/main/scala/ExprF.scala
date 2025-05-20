import cats.{ Applicative, Eval, Functor, Traverse }

import alleycats.{ Zero => `0`, One => `1` }

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

  implicit def kittensExprFTraverse(implicit `0`: `0`[?], `1`: `1`[?]): Traverse[ExprF] =
    new Traverse[ExprF]:
      override def foldLeft[A, B](xa: ExprF[A], b: B)(f: (B, A) => B): B =
        implicit val `0ʹ`: `0`[A] = `0`.asInstanceOf[`0`[A]]
        implicit val `1ʹ`: `1`[A] = `1`.asInstanceOf[`1`[A]]
        xa match
          case ValF(n: A) => f(b, n)
          case AddF(m, n) => f(f(b, m), n)
          case SubF(m, n) => f(f(b, m), n)
          case MulF(m, n) => f(f(b, m), n)
          case DivF(m, n) => f(f(b, m), n)
          case InvF(n)    => f(b, n)
          case ZeroF      => f(b, `0ʹ`.zero)
          case OneF       => f(b, `1ʹ`.one)
          case FacF(n, _) => f(b, n)
      override def foldRight[A, B](xa: ExprF[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
        implicit val `0ʹ`: `0`[A] = `0`.asInstanceOf[`0`[A]]
        implicit val `1ʹ`: `1`[A] = `1`.asInstanceOf[`1`[A]]
        xa match
          case ValF(n: A) => f(n, lb)
          case AddF(m, n) => f(m, f(n, lb))
          case SubF(m, n) => f(m, f(n, lb))
          case MulF(m, n) => f(m, f(n, lb))
          case DivF(m, n) => f(m, f(n, lb))
          case InvF(n)    => f(n, lb)
          case ZeroF      => f(`0ʹ`.zero, lb)
          case OneF       => f(`1ʹ`.one, lb)
          case FacF(n, _) => f(n, lb)
      override def traverse[G[_]: Applicative, A, B](xa: ExprF[A])(f: A => G[B]): G[ExprF[B]] =
        val G = Applicative[G]
        xa match
          case ValF(n: A) => G.map(f(n))(ValF(_))
          case AddF(m, n) => G.map2(f(m), f(n))(AddF(_, _))
          case SubF(m, n) => G.map2(f(m), f(n))(SubF(_, _))
          case MulF(m, n) => G.map2(f(m), f(n))(MulF(_, _))
          case DivF(m, n) => G.map2(f(m), f(n))(DivF(_, _))
          case InvF(n)    => G.map(f(n))(InvF(_))
          case it @ (ZeroF | OneF) => G.pure(it)
          case FacF(n, k) => G.map(f(n))(FacF(_, k))

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
