import scala.util.Random.{ nextInt, shuffle }

import alleycats.{ Zero => `0`, One => `1` }
import cats.instances.list.*
import cats.syntax.functor.*
import cats.syntax.traverse.*

import Expr.*

enum Op:
  case +, -, *, /, ~, `0`, `1`

def opsify(ls: List[List[Int]]): List[Expr[List[Int]]] =
  require(ls.size >= 2)
  shuffle {
    ls.sequence
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
      case Op.`0` => Zero
      case Op.`1` => One
  }

object Main:
  def main(args: Array[String]): Unit =

    val xs1 = opsify(List(List(1,2,3),List(2,3,4),List(0,4,5)))
    val xs2 = opsify(List(List(1,0,4),List(2,-1,5),List(0,2,3)))

    val xs3 = (xs1 ++ xs2)
      .sequence
      .map(_.map(_.toSet))

    val xs = xs3.map {
      shuffle(_)
        .take(2+nextInt(5))
        .reduce(_ & _)
    }

    {
      import scala.util.control.TailCalls.*
      type unit = Expr.Zero.type | Expr.One.type
      def eval(expr: Expr[Double])(implicit unit: unit, `0`: `0`[Double], `1`: `1`[Double]): Double =
        def evalʹ(xa: Expr[Double]): TailRec[Double] =
          xa match
            case Zero => done(`0`.zero)
            case One => done(`1`.one)
            case Val(n) => done(n)
            case Inv(xn) if Zero eq unit =>
              for
                n <- tailcall { evalʹ(xn) }
              yield
                `0`.zero - n
            case Inv(xn) if One eq unit =>
              for
                n <- tailcall { evalʹ(xn) }
              yield
                `1`.one / n
            case Add(xm, xn)       =>
              for
                m <- tailcall { evalʹ(xm) }
                n <- tailcall { evalʹ(xn) }
              yield
                m + n
            case Sub(xm, xn)       =>
              for
                m <- tailcall { evalʹ(xm) }
                n <- tailcall { evalʹ(xn) }
              yield
                m - n
            case Mul(xm, xn)       =>
              for
                m <- tailcall { evalʹ(xm) }
                n <- tailcall { evalʹ(xn) }
              yield
                m * n
            case Div(xm, xn)       =>
              for
                m <- tailcall { evalʹ(xm) }
                n <- tailcall { evalʹ(xn) }
              yield
                m / n
        evalʹ(expr).result

      given `0`[Double] = `0`(0d)
      given `1`[Double] = `1`(1d)
      given unit = Zero
      val lb = cats.Traverse[Expr].foldRight(Add(Sub(Zero, One), Val(1d)), cats.Eval.now(0d)) { (x, a) => a.map(x + _) }
    }

    {
      implicit val zero: `0`[Set[Int]] = `0`(Set.empty)
      implicit def one(implicit n: Int): `1`[Set[Int]] = `1`(Set(-n, n))
      implicit val universe: Set[Int] = Set.from(-5 to 5)

      given Int = 1

      println(show(xs))

      println(show(Val(eval(xs))))
    }
