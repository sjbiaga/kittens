import scala.util.Random.{ nextInt, shuffle }

import alleycats.{ Zero, One }
import cats.instances.list._
import cats.syntax.functor._
import cats.syntax.traverse._

import Expr._

enum Op:
  case +, -, *, /, ~, `0`, `1`

def opsify(ls: List[List[Int]]): List[Expr[List[Int]]] =
  require(ls.size >= 2)
  shuffle {
    ls.traverse(identity)
      .sliding(2, 3)
      .toList
  }
  .take(2+nextInt(5))
  .zipWithIndex
  .map {
    case ((List(lhs, rhs), idx)) =>
      if idx % 2 == 0
      then
        Op.+ -> (lhs, rhs)
      else if idx % 4 == 0
      then
        Op.* -> (lhs, rhs)
      else
        Op.- -> (lhs, rhs)
  }
  .map { it =>
    val lhs = Val(it._2._1)
    val rhs = Val(it._2._2)
    it._1 match
      case Op.+ => Add(lhs, rhs)
      case Op.- => Sub(lhs, rhs)
      case Op.* => Mul(lhs, rhs)
      case Op./ => Div(lhs, rhs)
      case Op.~ => Inv(rhs)
      case Op.`0` => Expr.Zero
      case Op.`1` => Expr.One
  }

object Main:
  def main(args: Array[String]): Unit =

    val xs1 = opsify(List(List(1,2,3),List(2,3,4),List(0,4,5)))
    val xs2 = opsify(List(List(1,0,4),List(2,-1,5),List(0,2,3)))

    val xs3 = (xs1 ++ xs2)
      .traverse(identity)
      .map(_.map(_.toSet))

    val xs = xs3.map {
      shuffle(_)
        .take(2+nextInt(5))
        .reduce(_ & _)
    }

    {
      implicit val zero: Zero[Set[Int]] = Zero(Set.empty)
      implicit def one(implicit n: Int): One[Set[Int]] = One(Set(-n, n))
      implicit val universe: Set[Int] = Set.from(-5 to 5)

      given Int = 1

      println(show(xs))

      println(show(Val(eval(xs))))
    }
