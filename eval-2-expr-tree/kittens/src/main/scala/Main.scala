import algebra.ring.DivisionRing
import cats._, cats.free._, cats.arrow._, Free._
import cats.syntax.all._

import Expr._, Tree._, Ring._

def treeify(R: DivisionRing[?]): FunctionK[Expr, Tree] =
  new FunctionK[Expr, Tree]:
    def apply[A](xa: Expr[A]): Tree[A] =
      implicit val Rʹ: DivisionRing[A] = R.asInstanceOf[DivisionRing[A]]
      xa match
        case Inv(n)    => Node(eval(xa), Op.Inv, None,           Some(apply(n)))
        case Add(m, n) => Node(eval(xa), Op.Add, Some(apply(m)), Some(apply(n)))
        case Mul(m, n) => Node(eval(xa), Op.Mul, Some(apply(m)), Some(apply(n)))
        case Sub(m, n) => Node(eval(xa), Op.Sub, Some(apply(m)), Some(apply(n)))
        case Div(m, n) => Node(eval(xa), Op.Div, Some(apply(m)), Some(apply(n)))
        case _         => Leaf(eval(xa))

case class Algorithms(n: Int):
  private def fibonacci(k: Int): Free[Expr, Expr[Int]] =
    if k < 2
    then
      liftF { if k < 1 then Zero else One }
    else
      for
        m <- defer { fibonacci(k - 2) }
        n <- defer { fibonacci(k - 1) }
      yield
        Add(m, n)
  private def factorial(k: Int): Free[Expr, Expr[Int]] =
    if k < 1
    then
      liftF { One }
    else
      for
        n <- defer { factorial(k - 1) }
      yield
        Mul(Val(k), n)
  def fib: Free[Expr, Expr[Int]] = fibonacci(n)
  def fac: Free[Expr, Expr[Int]] = factorial(n)

object Main:
  def main(args: Array[String]): Unit =
    val as = Algorithms(10)
    println(as.fib.mapK(treeify(kittensExprRing)).runTailRec.map(eval).result)
