[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

`Validated`
-----------

`Validated` is _not_ a monad transformer, and not a monad either: it lacks a `flatMap` method. Although such a method can be
easily constructed:

```Scala
def flatMap[EE >: E, B](f: A => Validated[EE, B]): Validated[EE, B] = // non-existing and not necessary
  this match {
    case i @ Invalid(_) => i
    case Valid(a)       => f(a)
  }
```

there is no point to it: `Validated` are `combine`d - with `Monoid`(s) - to "accumulate" errors (and values). However,
`Validated` has a `Functor` typeclass instance - and hence can be the effect of `WriterT`.

Methods à la `map`
------------------

Methods related to errors
-------------------------

Traversing or folding methods
-----------------------------

`to*` methods
-------------

Other methods
-------------

Methods from the companion object
---------------------------------

Exercise 08.8
=============

The requirements are the same as in
[Exercise 08.1](https://github.com/sjbiaga/kittens/blob/main/mt-6-WriterT/README.md#exercise-081), but this time use
`Validated` as the effect functor, in order to to catch divisions by `Zero`, both in the parser and builder. This asks to
`simplify` the right hand side
(see [Exercise 06.1](https://github.com/sjbiaga/kittens/blob/main/expr-simplify/README.md#exercise-061)). Put a check mark
`✓` to the right of the valid log messages, and an `✗` to the left of the error messages, which must be each collected as a
`Vector`. Once an expression becomes `Validated.Invalid`, the method `getOrElse` called on the `WriterT#value` of
`Validated[Vector[String], Expr[T]]` type must return `null`.

[Hint: use the following setup:

```Scala
import scala.util.control.TailCalls._
import scala.util.parsing.combinator.JavaTokenParsers

import cats.{ ~>, Monoid, MonoidK }
import cats.instances.string._
import cats.instances.vector._

import cats.data.{ Validated, WriterT }
import WriterT._

object Expr extends JavaTokenParsers:

  type unit = Expr.Zero.type | Expr.One.type

  type Validatedʹ[T] = Validated[Vector[String], T]

  type Writerʹ[T] = WriterT[Validatedʹ, String, T]

  type Exprʹ[T] = Writerʹ[Expr[T]]

  type Doubleʹ = WriterT[Validatedʹ, String, Double]

  given [T]: Conversion[Validatedʹ[T], T] = _.getOrElse(null.asInstanceOf[T])

  implicit def kittensExprMonoidKʹ(implicit unit: unit): MonoidK[Expr] =
    new MonoidK[Expr]:
      def empty[A]: Expr[A] = unit
      def combineK[A](_x: Expr[A], y: Expr[A]): Expr[A] = y // because of log.foldRight(...)(_.value.combine(_))

  implicit def kittensExprMonoidʹ[A: Monoid](implicit unit: unit): Monoid[Expr[A]] =
    kittensExprMonoidKʹ.algebra[A]

  def putʹ[T: Monoid](valʹ: T)(log: Writerʹ[T]*)(msg: String, isValid: Boolean = true)(implicit indent: String): Writerʹ[T] =
    val msgʹ = if isValid then Validated.valid(indent + msg + "✓") else Validated.invalid(Vector(indent + "✗" + msg))
    val valʹʹ = if isValid then Validated.Valid(valʹ) else Validated.invalid(Vector("✗" + msg))
    val valʹʹʹ = log.foldRight(valʹʹ)(_.value.combine(_))
    putT(valʹʹʹ)(log.foldRight(msgʹ)(_.swap.value.combine(_)).fold(_.mkString("", "\n", ""), identity) + "\n")

  val simplify: unit ?=> Expr ~> Expr =
    new (Expr ~> Expr):
      val unit = summon[unit]
      def apply[T](expr: Expr[T]): Expr[T] =
        def applyʹ(xa: Expr[T]): TailRec[Expr[T]] =
          xa match
            case Add(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                if n eq Zero then m
                else if m eq Zero then n
                else Add(m, n)
            case Sub(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                if n eq Zero then m
                else if (m eq Zero) && (unit eq Zero) then Inv(n)
                else Sub(m, n)
            case Mul(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                if n eq One then m
                else if m eq One then n
                else if (n eq Zero) || (m eq Zero) then Zero
                else Mul(m, n)
            case Div(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                if n eq One then m
                else if (m eq One) && (unit eq One) then Inv(n)
                else if m eq Zero then Zero
                else Div(m, n)
            case Inv(xn)     =>
              for
                n <- tailcall { applyʹ(xn) }
              yield
                Inv(n)
            case it          => done(it)
        applyʹ(expr).result
```

where `simplify` has been rewritten in a stack safe manner.

A typical use of the `kittensExprMonoidʹ` is where we form `Add(lhs, rhs)` from `lhs` and `rhs`. In the snippet:

```Scala
    val valʹʹ = if isValid then Validated.Valid(valʹ) else Validated.invalid(Vector("✗" + msg))
    val valʹʹʹ = log.foldRight(valʹʹ)(_.value.combine(_))
```

`valʹ` is `Add(lhs, rhs)`, while `log` is `Seq(lhs, rhs)`; when we do `log.foldRight`, first `rhs.value` will be `combine`d
with `valʹʹ`, which by `kittensExprMonoidʹ` yields the latter; second, `lhs.value` will be `combine`d with `valʹʹ`, which by
`kittensExprMonoidʹ` yields the latter; so - if valid - `valʹ` will be the result which gets `putT` - i.e., `Add(lhs, rhs)`.]

Solution - Part 1 - Parser
--------------------------

```Scala
  def expr(implicit unit: unit, indent: String): Parser[Exprʹ[Double]] =
    term ~ rep(("+"|"-") ~ term) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "+" ~ rhs) =>
          putʹ(Add(lhs.value, rhs.value))(lhs, rhs)("addition")
        case (lhs, "-" ~ rhs) =>
          putʹ(Sub(lhs.value, rhs.value))(lhs, rhs)("subtraction")
      }
    }

  def term(implicit unit: unit, indent: String): Parser[Exprʹ[Double]] =
    factor ~ rep(("*"|"/") ~ factor) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "*" ~ rhs) =>
          putʹ(Mul(lhs.value, rhs.value))(lhs, rhs)("multiplication")
        case (lhs, "/" ~ rhs)
          if (unit eq One) && {
            rhs.value match
              case null => false
              case rhsʹ =>
                simplify(rhsʹ) match
                  case Zero | Val(0) | Val(0d) => true
                  case _ => false
          } =>
          putʹ(Div(lhs.value, rhs.value))(lhs, rhs)(s"division by zero: ${lhs.value: Expr[Double]} ÷ ${rhs.value: Expr[Double]}", false)
        case (lhs, "/" ~ rhs) =>
          putʹ(Div(lhs.value, rhs.value))(lhs, rhs)("division")
      }
    }

  def factor(implicit unit: unit, indent: String): Parser[Exprʹ[Double]] =
    ("+"|"-") ~ literal ^^ {
      case "-" ~ rhs if unit eq Zero =>
        putʹ(Inv(rhs.value))(rhs)("unary negation")
      case "+" ~ rhs =>
        putʹ(Add(Zero, rhs.value))(rhs)("addition with zero")
      case "-" ~ rhs =>
        putʹ(Sub(Zero, rhs.value))(rhs)("subtraction from zero")
    } |
    literal ^^ { identity }

  def literal(implicit unit: unit, indent: String): Parser[Exprʹ[Double]] =
    floatingPointNumber ^^ { it =>
      it.toDouble match
        case 0d => putʹ(Zero: Expr[Double])()("constant zero: Double")
        case 1d => putʹ(One: Expr[Double])()("constant one: Double")
        case n  => putʹ(Val(n))()(s"value $n: Double")
    } |
    "("~> expr(using unit, indent + "  ") <~")" ^^ { _.tell(s"${indent}parentheses\n") }

  implicit class ExprInterpolator(private val sc: StringContext) extends AnyVal:
    def x(args: Any*)(implicit unit: unit): Exprʹ[Double] =
      val inp = (sc.parts zip (args :+ "")).foldLeft("") {
        case (r, (p, a)) => r + p + a
      }
      parseAll(expr(using unit, ""), inp) match
        case Success(it, _) => it
```

Solution - Part 2 - Builder
---------------------------

The `swap` method remains the same.

```Scala
  final case class Builder[T: Monoid](lhs: Exprʹ[T], private var save: List[Exprʹ[T]])(using indent: String)(using unit):
    def indent(rhs: Exprʹ[T]): Exprʹ[T] =
      rhs.mapWritten(_.split("\n").map(indent + _).mkString("", "\n", "\n"))
    private def fill(n: Int) = List.fill(0 max n)(())
    def swapping =
      Builder(putʹ(swap(lhs.value))(lhs)("swapping"), save)
    def add(rhs: Expr[T], n: Int = 1)(using m: Option[String] = None) =
      Builder (
        {
          implicit val indentʹ = if m eq None then indent else ""
          fill(n)
            .foldLeft(lhs) {
              (lhs, _) =>
                putʹ(Add(lhs.value, rhs))(lhs)(m.map(_ + indent + "adding").getOrElse("adding"))
            }
        }
        , save
      )
    def addʹ(rhs: Exprʹ[T], n: Int = 1)(using m: Option[String] = None) =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              val rhsʹ = if m eq None then indent(rhs) else rhs
              putʹ(Add(lhs.value, rhsʹ.value))(lhs, rhsʹ)(m.map(_ + indent + "adding").getOrElse("adding"))
          }
        , save
      )
    def subtract(rhs: Expr[T], n: Int = 1)(using m: Option[String] = None) =
      Builder (
        {
          implicit val indentʹ = if m eq None then indent else ""
          fill(n)
            .foldLeft(lhs) {
              (lhs, _) =>
                putʹ(Sub(lhs.value, rhs))(lhs)(m.map(_ + indent + "subtracting").getOrElse("subtracting"))
            }
        }
        , save
      )
    def subtractʹ(rhs: Exprʹ[T], n: Int = 1)(using m: Option[String] = None) =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              val rhsʹ = if m eq None then indent(rhs) else rhs
              putʹ(Sub(lhs.value, rhsʹ.value))(lhs, rhsʹ)(m.map(_ + indent + "subtracting").getOrElse("subtracting"))
          }
        , save
      )
    def multiply(rhs: Expr[T], n: Int = 1)(using m: Option[String] = None) =
      Builder (
        {
          implicit val indentʹ = if m eq None then indent else ""
          fill(n)
            .foldLeft(lhs) {
              (lhs, _) =>
                putʹ(Mul(lhs.value, rhs))(lhs)(m.map(_ + indent + "multiplying").getOrElse("multiplying"))
            }
        }
        , save
      )
    def mutiplyʹ(rhs: Exprʹ[T], n: Int = 1)(using m: Option[String] = None) =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              val rhsʹ = if m eq None then indent(rhs) else rhs
              putʹ(Mul(lhs.value, rhsʹ.value))(lhs, rhsʹ)(m.map(_ + indent + "multiplying").getOrElse("multiplying"))
          }
        , save
      )
    def divide(rhs: Expr[T], n: Int = 1)(using m: Option[String] = None) =
      Builder (
        {
          val isValid = simplify(rhs) ne Zero
          implicit val indentʹ = if m eq None then indent else ""
          fill(n)
            .foldLeft(lhs) {
              (lhs, _) =>
                val msg = s"""dividing${if isValid then "" else s" by zero: (${lhs.value: Expr[T]} ÷ ${rhs: Expr[T]})"}"""
                putʹ(Div(lhs.value, rhs))(lhs)(msg, isValid)
            }
        }
        , save
      )
    def divideʹ(rhs: Exprʹ[T], n: Int = 1)(using m: Option[String] = None) =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              val rhsʹ = if m eq None then indent(rhs) else rhs
              putʹ(Div(lhs.value, rhsʹ.value))(lhs, rhsʹ)(m.map(_ + indent + "dividing").getOrElse("dividing"))
          }
        , save
      )
    def invert(n: Int = 1): Builder[T] =
      Builder (
        fill(n)
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
      f(self, lhs.value)(using Some(putʹ(Zero)(lhs)("closing").swap.value))
        .invert(invert)
    def closeʹ(f: (Builder[T], Exprʹ[T]) => Option[String] ?=> Builder[T], invert: Int = 0) =
      implicit val indent = this.indent.substring(2)
      val self = Builder(save.head, save.tail)
      f(self, lhs)(using Some("closing✓\n"))
        .invert(invert)
  object Builder:
    def start[T: Monoid](using unit)= From[T]("starting", Nil)(using "")
    final case class From[T: Monoid](msg: String, save: List[Exprʹ[T]])(using indent: String)(using unit):
      def apply(lhs: Expr[T]): Builder[T] =
        Builder(putʹ(lhs)()(msg), save)(using indent + "  ")
      def apply(lhs: Exprʹ[T]): Builder[T] =
        Builder(putʹ(lhs.value: Expr[T])(lhs)(msg), save)(using indent + "  ")
```

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md)
