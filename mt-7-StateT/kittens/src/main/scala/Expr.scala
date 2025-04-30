import scala.util.control.TailCalls._
import scala.util.parsing.combinator.JavaTokenParsers

import algebra.ring.{ DivisionRing, Ring }
import alleycats.{ Zero => `0`, One => `1` }

import cats.~>

import Expr._
import Tree._

enum Expr[+T]:
  case Add[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case Sub[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case Zero extends Expr[Nothing]
  case Mul[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case Div[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case One extends Expr[Nothing]
  case Inv[+T](rhs: Expr[T]) extends Expr[T]
  case Val[T](n: T) extends Expr[T]

object Expr extends JavaTokenParsers:

  type unit = Expr.Zero.type | Expr.One.type

  implicit val kittensDoubleRing: DivisionRing[Double] =
    new DivisionRing[Double]:
      override val zero = 0d
      override val one = 1d
      override def negate(n: Double) = 0d - n
      override def reciprocal(n: Double) = 1d / n
      override def plus(m: Double, n: Double) = m + n
      override def minus(m: Double, n: Double) = m - n
      override def times(m: Double, n: Double) = m * n
      override def div(m: Double, n: Double) = m / n

  def expressify(implicit R: DivisionRing[?]): unit ?=> Tree ~> Expr =
      new (Tree ~> Expr):
        def apply[A](tree: Tree[A]): Expr[A] =
          val (zero, one) = (R.zero, R.one)
          def applyʹ(ta: Tree[A]): TailRec[Expr[A]] =
            ta match
              case Node(_, Op.Inv, _,       Some(n)) =>
                for
                  nʹ <- tailcall { applyʹ(n) }
                yield
                  Inv(nʹ)
              case Node(_, Op.Add, Some(m), Some(n)) =>
                for
                  mʹ <- tailcall { applyʹ(m) }
                  nʹ <- tailcall { applyʹ(n) }
                yield
                  Add(mʹ, nʹ)
              case Node(_, Op.Sub, Some(m), Some(n)) =>
                for
                  mʹ <- tailcall { applyʹ(m) }
                  nʹ <- tailcall { applyʹ(n) }
                yield
                  Sub(mʹ, nʹ)
              case Node(_, Op.Mul, Some(m), Some(n)) =>
                for
                  mʹ <- tailcall { applyʹ(m) }
                  nʹ <- tailcall { applyʹ(n) }
                yield
                  Mul(mʹ, nʹ)
              case Node(_, Op.Div, Some(m), Some(n)) =>
                for
                  mʹ <- tailcall { applyʹ(m) }
                  nʹ <- tailcall { applyʹ(n) }
                yield
                  Div(mʹ, nʹ)
              case Leaf(`zero`)                      => done(Zero)
              case Leaf(`one`)                       => done(One)
              case Leaf(r)                           => done(Val(r))
          applyʹ(tree).result

  def expr(implicit unit: unit): Parser[Expr[Int | Double]] =
    term ~ rep(("+"|"-") ~ term) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "+" ~ rhs) => Add(lhs, rhs)
        case (lhs, "-" ~ rhs) => Sub(lhs, rhs)
      }
    }

  def term(implicit unit: unit): Parser[Expr[Int | Double]] =
    factor ~ rep(("*"|"/") ~ factor) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "*" ~ rhs) => Mul(lhs, rhs)
        case (lhs, "/" ~ rhs) => Div(lhs, rhs)
      }
    }

  def factor(implicit unit: unit): Parser[Expr[Int | Double]] =
    ("+"|"-") ~ literal ^^ {
      case "-" ~ rhs if unit eq Zero => Inv(rhs)
      case "+" ~ rhs => Add(Zero, rhs)
      case "-" ~ rhs => Sub(Zero, rhs)
    } |
    literal ^^ { identity }

  def literal(implicit unit: unit): Parser[Expr[Int | Double]] =
    floatingPointNumber ^^ { it =>
      it.toDouble match
        case 0d => Zero
        case 1d => One
        case n => Val(n)
    } |
    decimalNumber ^^ { it =>
      it.toInt match
        case 0 => Zero
        case 1 => One
        case n => Val(n)
    } |
    "("~> expr <~")" ^^ { identity }

  implicit class ExprInterpolator(private val sc: StringContext) extends AnyVal:
    def x(args: Any*)(implicit unit: unit): Expr[Int | Double] =
      val inp = (sc.parts zip (args :+ "")).foldLeft("") {
        case (r, (p, a)) => r + p + a
      }
      parseAll(expr, inp) match
        case Success(it, _) => it

  val swap: unit ?=> Expr ~> Expr =
    new (Expr ~> Expr):
      def apply[T](expr: Expr[T]): Expr[T] =
        def applyʹ(xa: Expr[T]): TailRec[Expr[T]] =
          xa match
            case Zero        => done(One)
            case One         => done(Zero)
            case Add(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Mul(m, n)
            case Sub(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Div(m, n)
            case Mul(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Add(m, n)
            case Div(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Sub(m, n)
            case Inv(Zero)
              if summon[unit] eq One => applyʹ(Div(One, Zero))
            case Inv(xn)     =>
              for
                n <- tailcall { applyʹ(xn) }
              yield
                Inv(n)
            case it          => done(it)
        applyʹ(expr).result

  def eval[A](expr: Expr[A])(implicit R: DivisionRing[A], unit: unit, `0`: `0`[A], `1`: `1`[A]): A =
    def evalʹ(xa: Expr[A]): TailRec[A] =
      xa match
        case Zero => done(`0`.zero)
        case One => done(`1`.one)
        case Val(n) => done(n)
        case Inv(xn) if Zero eq unit =>
          for
            n <- tailcall { evalʹ(xn) }
          yield
            R.minus(`0`.zero, n)
        case Inv(xn) if One eq unit =>
          for
            n <- tailcall { evalʹ(xn) }
          yield
            R.div(`1`.one, n)
        case Add(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            R.plus(m, n)
        case Sub(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            R.times(m, n)
        case Mul(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            R.times(m, n)
        case Div(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            R.div(m, n)
    evalʹ(expr).result

  final case class Builder[T](lhs: Expr[T], private var save: List[Expr[T]]):
    def fill(n: Int)(rhs: Expr[T]) = List.fill(0 max n)(rhs)
    def swapping(implicit unit: unit) = Builder(swap(lhs), save)
    def add(rhs: Expr[T], n: Int = 1) = Builder(fill(n)(rhs).foldLeft(lhs)(Add(_, _)), save)
    def subtract(rhs: Expr[T], n: Int = 1) = Builder(fill(n)(rhs).foldLeft(lhs)(Sub(_, _)), save)
    def multiply(rhs: Expr[T], n: Int = 1) = Builder(fill(n)(rhs).foldLeft(lhs)(Mul(_, _)), save)
    def divide(rhs: Expr[T], n: Int = 1) = Builder(fill(n)(rhs).foldLeft(lhs)(Div(_, _)), save)
    def invert(n: Int = 1): Builder[T] = Builder(List.fill(0 max n)(()).foldLeft(lhs) { (lhs, _) => Inv(lhs) }, save)
    def open = Builder.From(lhs :: save)
    def close(f: (Builder[T], Expr[T]) => Builder[T], invert: Int = 0) =
      val self = Builder(save.head, save.tail)
      f(self, lhs).invert(invert)
  object Builder:
    def start[T] = From[T](Nil)
    final case class From[T](save: List[Expr[T]]):
      def apply(lhs: Expr[T]): Builder[T] = Builder(lhs, save)
