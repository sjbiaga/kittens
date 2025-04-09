import algebra.ring.DivisionRing

import Expr._

object Ring:
  implicit val kittensIntRing: DivisionRing[Int] =
   new DivisionRing[Int]:
     override val zero = 0
     override val one = 1
     override def negate(n: Int) = 0 - n
     override def reciprocal(n: Int) = ???
     override def plus(m: Int, n: Int) = m + n
     override def minus(m: Int, n: Int) = m - n
     override def times(m: Int, n: Int) = m * n
     override def div(m: Int, n: Int) = m / n

implicit def kittensExprRing[A]: DivisionRing[Expr[A]] =
  new DivisionRing[Expr[A]]:
    override val zero = Zero
    override val one = One
    override def negate(n: Expr[A]) = Inv(n)
    override def reciprocal(n: Expr[A]) = ???
    override def plus(m: Expr[A], n: Expr[A]) = Add(m, n)
    override def minus(m: Expr[A], n: Expr[A]) = Sub(m, n)
    override def times(m: Expr[A], n: Expr[A]) = Mul(m, n)
    override def div(m: Expr[A], n: Expr[A]) = Div(m, n)
