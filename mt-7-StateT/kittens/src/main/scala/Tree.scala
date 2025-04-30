import scala.util.control.TailCalls._

import algebra.ring.DivisionRing
import alleycats.{ Zero => `0`, One => `1` }

import cats.~>

import Expr._
import Tree._

enum Op:
  case Add, Sub, Mul, Div, Inv

enum Tree[+T]:
  val result: T
  case Leaf[+T](override val result: T) extends Tree[T]
  case Node[+T](override val result: T,
                operator: Op,
                left: Option[Tree[T]],
                right: Option[Tree[T]]) extends Tree[T]

object Tree:
  
  def treeify(implicit R: DivisionRing[?], unit: unit, `0`: `0`[?], `1`: `1`[?]): Expr ~> Tree =
    new (Expr ~> Tree):
      def apply[A](expr: Expr[A]): Tree[A] =
        given DivisionRing[A] = R.asInstanceOf[DivisionRing[A]]
        given `0`[A] = `0`.asInstanceOf[`0`[A]]
        given `1`[A] = `1`.asInstanceOf[`1`[A]]
        def applyʹ(xa: Expr[A]): TailRec[Tree[A]] =
          xa match
            case Add(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Node(eval(xa), Op.Add, Some(m), Some(n))
            case Sub(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Node(eval(xa), Op.Sub, Some(m), Some(n))
            case Mul(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Node(eval(xa), Op.Mul, Some(m), Some(n))
            case Div(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Node(eval(xa), Op.Div, Some(m), Some(n))
            case Inv(xn)     =>
              for
                n <- tailcall { applyʹ(xn) }
              yield
                Node(eval(xa), Op.Inv, None, Some(n))
            case _           => done(Leaf(eval(xa)))
        applyʹ(expr).result