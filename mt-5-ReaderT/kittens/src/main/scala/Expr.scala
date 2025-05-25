import scala.util.control.TailCalls._

import alleycats.{ Zero => `0`, One => `1` }

enum Expr[+T]:
  case Add[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case Sub[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case Zero extends Expr[Nothing]
  case Mul[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case Div[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case One extends Expr[Nothing]
  case Inv[+T](rhs: Expr[T]) extends Expr[T]
  case Val[T](n: T) extends Expr[T]

object Expr:

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
