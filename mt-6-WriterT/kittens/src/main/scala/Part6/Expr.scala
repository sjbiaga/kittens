package Exercise_08_1
package Part6

import scala.util.control.TailCalls._
import scala.util.parsing.combinator.JavaTokenParsers

import cats.{ ~>, Id }
import cats.instances.string._

import cats.data.Writer
import cats.data.WriterT._

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

  type Writerʹ[T] = Writer[String, T]

  type Exprʹ[T] = Writerʹ[Expr[T]]

  type Doubleʹ = Writer[String, Double]

  def putʹ[T, U](valʹ: T)(log: Writerʹ[U]*)(msg: String)(implicit indent: String): Writerʹ[T] =
    putT[Id, String, T](valʹ)(log.foldRight(indent + msg)(_.swap.value + _) + "\n")

  def putʹ[T](valʹ: T)(msg: String)(implicit indent: String): Writerʹ[T] =
    putʹ(valʹ)()(msg)

  def expr(implicit unit: unit, indent: String): Parser[Exprʹ[Int | Double]] =
    term ~ rep(("+"|"-") ~ term) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "+" ~ rhs) =>
          putʹ(Add(lhs.value, rhs.value))(lhs, rhs)("addition")
        case (lhs, "-" ~ rhs) =>
          putʹ(Sub(lhs.value, rhs.value))(lhs, rhs)("subtraction")
      }
    }

  def term(implicit unit: unit, indent: String): Parser[Exprʹ[Int | Double]] =
    factor ~ rep(("*"|"/") ~ factor) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "*" ~ rhs) =>
          putʹ(Mul(lhs.value, rhs.value))(lhs, rhs)("multiplication")
        case (lhs, "/" ~ rhs) =>
          putʹ(Div(lhs.value, rhs.value))(lhs, rhs)("division")
      }
    }

  def factor(implicit unit: unit, indent: String): Parser[Exprʹ[Int | Double]] =
    ("+"|"-") ~ literal ^^ {
      case "-" ~ rhs if unit eq Zero =>
        putʹ(Inv(rhs.value))(rhs)("unary negation")
      case "+" ~ rhs =>
        putʹ(Add(Zero, rhs.value))(rhs)("addition with zero")
      case "-" ~ rhs =>
        putʹ(Sub(Zero, rhs.value))(rhs)("subtraction from zero")
    } |
    literal ^^ { identity }

  def literal(implicit unit: unit, indent: String): Parser[Exprʹ[Int | Double]] =
    floatingPointNumber ^^ { it =>
      it.toDouble match
        case 0d => putʹ(Zero)("constant zero: Double")
        case 1d => putʹ(One)("constant one: Double")
        case n  => putʹ(Val(n))(s"value $n: Double")
    } |
    decimalNumber ^^ { it =>
      it.toInt match
        case 0 => putʹ(Zero)("constant zero: Int")
        case 1 => putʹ(One)("constant one: Int")
        case n => putʹ(Val(n))(s"value $n: Int")
    } |
    "("~> expr(using unit, indent + "  ") <~")" ^^ { _.tell(s"${indent}parentheses\n") }

  implicit class ExprInterpolator(private val sc: StringContext) extends AnyVal:
    def x(args: Any*)(implicit unit: unit): Exprʹ[Int | Double] =
      val inp = (sc.parts zip (args :+ "")).foldLeft("") {
        case (r, (p, a)) => r + p + a
      }
      parseAll(expr(using unit, ""), inp) match
        case Success(it, _) => it

  def eval(expr: Expr[Double])(implicit unit: unit): Doubleʹ =
    implicit val indent: String = ""
    def evalʹ(xa: Expr[Double]): TailRec[Doubleʹ] =
      xa match
        case Zero              => done(putʹ(0d)("constant zero"))
        case One               => done(putʹ(1d)("constant one"))
        case Val(n)            => done(putʹ(n)(s"value $n"))
        case Inv(xn) if Zero eq unit =>
          for
            n <- tailcall { evalʹ(xn) }
          yield
            putʹ(0d - n.value)(n)("invert")
        case Inv(xn) if One eq unit =>
          for
            n <- tailcall { evalʹ(xn) }
          yield
            putʹ(1d / n.value)(n)("invert")
        case Add(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            putʹ(m.value + n.value)(m, n)("plus")
        case Sub(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            putʹ(m.value - n.value)(m, n)("minus")
        case Mul(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            putʹ(m.value * n.value)(m, n)("times")
        case Div(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            putʹ(m.value / n.value)(m, n)("divides")
    evalʹ(expr).result

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
                Add(m, n)
            case Sub(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Sub(m, n)
            case Mul(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Mul(m, n)
            case Div(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Div(m, n)
            case Inv(Zero)
              if summon[unit] eq One => applyʹ(Div(One, Zero))
            case Inv(xn)     =>
              for
                n <- tailcall { applyʹ(xn) }
              yield
                Inv(n)
            case it          => done(it)
        applyʹ(expr).result

  final case class Builder[T](lhs: Exprʹ[T], private var save: List[Exprʹ[T]])(implicit indent: String):
    def indent(rhs: Exprʹ[T]): Exprʹ[T] =
      rhs.mapWritten(_.split("\n").map(indent + _).mkString("", "\n", "\n"))
    private def fill(rhs: Expr[T])(n: Int) = List.fill(0 max n)(rhs)
    private def fill(rhs: Exprʹ[T])(n: Int) = List.fill(0 max n)(rhs)
    def swapping(implicit unit: unit) =
      Builder(putʹ(swap(lhs.value))(lhs)("swapping"), save)
    def add(rhs: Expr[T], n: Int = 1)(using m: Option[String] = None) =
      val indentʹ = if m eq None then indent else ""
      Builder (
        fill(rhs)(n)
          .foldLeft(lhs) {
            (lhs, rhs) =>
              putʹ(Add(lhs.value, rhs))(lhs)(m.map(_ + indent + "adding").getOrElse("adding"))(using indentʹ)
          }
        , save
      )
    def addʹ(rhs: Exprʹ[T], n: Int = 1)(using m: Option[String] = None) =
      Builder (
        fill(rhs)(n)
          .foldLeft(lhs) {
            (lhs, rhs) =>
              val rhsʹ = if m eq None then indent(rhs) else rhs
              putʹ(Add(lhs.value, rhsʹ.value))(lhs, rhsʹ)(m.map(_ + indent + "adding").getOrElse("adding"))
          }
        , save
      )
    def subtract(rhs: Expr[T], n: Int = 1)(using m: Option[String] = None) =
      val indentʹ = if m eq None then indent else ""
      Builder (
        fill(rhs)(n)
          .foldLeft(lhs) {
            (lhs, rhs) =>
              putʹ(Sub(lhs.value, rhs))(lhs)(m.map(_ + indent + "subtracting").getOrElse("subtracting"))(using indentʹ)
          }
        , save
      )
    def subtractʹ(rhs: Exprʹ[T], n: Int = 1)(using m: Option[String] = None) =
      Builder (
        fill(rhs)(n)
          .foldLeft(lhs) {
            (lhs, rhs) =>
              val rhsʹ = if m eq None then indent(rhs) else rhs
              putʹ(Sub(lhs.value, rhsʹ.value))(lhs, rhsʹ)(m.map(_ + indent + "subtracting").getOrElse("subtracting"))
          }
        , save
      )
    def multiply(rhs: Expr[T], n: Int = 1)(using m: Option[String] = None) =
      val indentʹ = if m eq None then indent else ""
      Builder (
        fill(rhs)(n)
          .foldLeft(lhs) {
            (lhs, rhs) =>
              putʹ(Mul(lhs.value, rhs))(lhs)(m.map(_ + indent + "multiplying").getOrElse("multiplying"))(using indentʹ)
          }
        , save
      )
    def mutiplyʹ(rhs: Exprʹ[T], n: Int = 1)(using m: Option[String] = None) =
      Builder (
        fill(rhs)(n)
          .foldLeft(lhs) {
            (lhs, rhs) =>
              val rhsʹ = if m eq None then indent(rhs) else rhs
              putʹ(Mul(lhs.value, rhsʹ.value))(lhs, rhsʹ)(m.map(_ + indent + "multiplying").getOrElse("multiplying"))
          }
        , save
      )
    def divide(rhs: Expr[T], n: Int = 1)(using m: Option[String] = None) =
      val indentʹ = if m eq None then indent else ""
      Builder (
        fill(rhs)(n)
          .foldLeft(lhs) {
            (lhs, rhs) =>
              putʹ(Div(lhs.value, rhs))(lhs)(m.map(_ + indent + "dividing").getOrElse("dividing"))(using indentʹ)
          }
        , save
      )
    def divideʹ(rhs: Exprʹ[T], n: Int = 1)(using m: Option[String] = None) =
      Builder (
        fill(rhs)(n)
          .foldLeft(lhs) {
            (lhs, rhs) =>
              val rhsʹ = if m eq None then indent(rhs) else rhs
              putʹ(Div(lhs.value, rhsʹ.value))(lhs, rhsʹ)(m.map(_ + indent + "dividing").getOrElse("dividing"))
          }
        , save
      )
    def invert(n: Int = 1): Builder[T] =
      Builder (
        List.fill(0 max n)(())
          .foldLeft(lhs) {
            (lhs, _) =>
              putʹ(Inv(lhs.value))(lhs)("inverting")
          }
        , save
      )
    inline def open = Builder.From("opening", lhs :: save)
    inline def openʹ = open
    def close(f: (Builder[T], Expr[T]) => Option[String] ?=> Builder[T], invert: Int = 0) =
      implicit val indent = this.indent.substring(2)
      val self = Builder(save.head, save.tail)
      f(self, lhs.value)(using Some(putʹ(())(lhs)("closing").swap.value))
        .invert(invert)
    def closeʹ(f: (Builder[T], Exprʹ[T]) => Option[String] ?=> Builder[T], invert: Int = 0) =
      implicit val indent = this.indent.substring(2)
      val self = Builder(save.head, save.tail)
      f(self, lhs)(using Some("closing\n"))
        .invert(invert)
  object Builder:
    def start[T] = From[T]("starting", Nil)(using "")
    final case class From[T](msg: String, save: List[Exprʹ[T]])(implicit indent: String):
      def apply(lhs: Expr[T]): Builder[T] =
        Builder(putʹ(lhs)(msg), save)(using indent + "  ")
      def apply(lhs: Exprʹ[T]): Builder[T] =
        Builder(putʹ(lhs.value)(lhs)(msg), save)(using indent + "  ")
