import cats.free.*, Free.*
import cats.syntax.all.*

import Expr.*, Tree.*, Ring.*

case class Algorithmsʹ(n: Int):
  private def fibonacci(k: Int): Free[Tree, Tree[Expr[Int]]] =
    if k < 2
    then
      liftF { Leaf(Leaf(if k < 1 then Zero else One)) }
    else
      for
        m <- defer { fibonacci(k - 2) }
        n <- defer { fibonacci(k - 1) }
      yield
        Node(Add(m.result, n.result), Op.Add, Some(m), Some(n))
  private def factorial(k: Int): Free[Tree, Tree[Expr[Int]]] =
    if k < 1
    then
      liftF { Leaf(Leaf(One)) }
    else
      for
        n <- defer { factorial(k - 1) }
      yield
        Node(Mul(Val(k), n.result), Op.Mul, Some(Leaf(Val(k))), Some(n))
  def fib: Free[Tree, Tree[Expr[Int]]] = fibonacci(n)
  def fac: Free[Tree, Tree[Expr[Int]]] = factorial(n)

object Mainʹ:
  def main(args: Array[String]): Unit =
    val asʹ = Algorithmsʹ(10)
    println(asʹ.fac.runTailRec.flatten.map(eval).result)
