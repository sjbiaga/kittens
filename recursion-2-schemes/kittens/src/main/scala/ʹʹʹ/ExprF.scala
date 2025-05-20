package ʹʹʹ

import cats.Functor, cats.syntax.functor._

sealed trait ExprF[+R]
case class AddF[+R](lhs: R, rhs: R) extends ExprF[R]
case class SubF[+R](lhs: R, rhs: R) extends ExprF[R]
case object ZeroF extends ExprF[Nothing]
case class MulF[+R](lhs: R, rhs: R) extends ExprF[R]
case class DivF[+R](lhs: R, rhs: R) extends ExprF[R]
case object OneF extends ExprF[Nothing]
case class InvF[+R](rhs: R) extends ExprF[R]
case class ValF[T](n: T) extends ExprF[Nothing]
case class IfNegF[+R](cond: R, `then`: R, `else`: R) extends ExprF[R]
case class VarF(identifier: String) extends ExprF[Nothing]

object ExprF:

  implicit val kittensExprFunctor: Functor[ExprF] =
     new Functor[ExprF]:
       override def map[A, B](xa: ExprF[A])(f: A => B): ExprF[B] =
         xa match
           case AddF(lhs, rhs)  => AddF(f(lhs), f(rhs))
           case SubF(lhs, rhs)  => SubF(f(lhs), f(rhs))
           case MulF(lhs, rhs)  => MulF(f(lhs), f(rhs))
           case DivF(lhs, rhs)  => DivF(f(lhs), f(rhs))
           case InvF(rhs)       => InvF(f(rhs))
           case IfNegF(c, t, e) => IfNegF(f(c), f(t), f(e))
           case it @ (ValF(_) | VarF(_) | ZeroF | OneF) => it

  final case class Fix[F[_]](unfix: F[Fix[F]])

  def cata[F[_]: Functor, A](f: F[A] => A): Fix[F] => A =
    fix => f(fix.unfix map cata(f))

  type Expr = Fix[ExprF]

  // smart constructors
  val Zero: Expr = Fix(ZeroF)
  val One: Expr = Fix(OneF)
  def Add(lhs: Expr, rhs: Expr): Expr = Fix(AddF(lhs, rhs))
  def Sub(lhs: Expr, rhs: Expr): Expr = Fix(SubF(lhs, rhs))
  def Mul(lhs: Expr, rhs: Expr): Expr = Fix(MulF(lhs, rhs))
  def Div(lhs: Expr, rhs: Expr): Expr = Fix(DivF(lhs, rhs))
  def Inv(rhs: Expr): Expr = Fix(InvF(rhs))
  def Val[T](n: T): Expr = Fix(ValF(n))
  def IfNeg(cond: Expr, `then`: Expr, `else`: Expr): Expr = Fix(IfNegF(cond, `then`, `else`))
  def Var(id: String): Expr = Fix(VarF(id))

  def vars(xa: Expr): Set[String] = cata(varsʹ)(xa)

  private val varsʹ: ExprF[Set[String]] => Set[String] = {
    case VarF(id)        => Set(id)
    case AddF(lhs, rhs)  => lhs ++ rhs
    case SubF(lhs, rhs)  => lhs ++ rhs
    case MulF(lhs, rhs)  => lhs ++ rhs
    case DivF(lhs, rhs)  => lhs ++ rhs
    case InvF(rhs)       => rhs
    case IfNegF(c, t, e) => c ++ t ++ e
    case (ValF(_) | ZeroF | OneF) => Set.empty
  }

  def subst(xa: Expr)(using Map[String, Expr]): Expr = cata(substʹ)(xa)

  private val substʹ: Map[String, Expr] ?=> ExprF[Expr] => Expr = substitution ?=> {
    case it @ VarF(id) => substitution.getOrElse(id, Fix(it))
    case it            => Fix(it)
  }

  def eval(xa: Expr)(using Map[String, Long]): Option[Long] = cata(evalʹ)(xa)

  val evalʹ: Map[String, Long] ?=> ExprF[Option[Long]] => Option[Long] = env ?=> {
    case AddF(lhs, rhs)   => (lhs zip rhs).map(_ + _)
    case SubF(lhs, rhs)   => (lhs zip rhs).map(_ - _)
    case MulF(lhs, rhs)   => (lhs zip rhs).map(_ * _)
    case DivF(lhs, rhs)   => (lhs zip rhs).map(_ / _)
    case InvF(rhs)        => rhs.map(0 - _)
    case IfNegF(c, t, e)  => c.flatMap { if (_: Long) < 0 then t else e}
    case ValF(n: Long)    => Some(n)
    case VarF(id)         => env.get(id)
    case ZeroF            => Some(0)
    case OneF             => Some(1)
  }
