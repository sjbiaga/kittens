[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-5-ReaderT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-7-StateT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

[`WriterT`](https://typelevel.org/cats/datatypes/writert.html)
--------------------------------------------------------------

Methods à la `map` or `flatMap`
-------------------------------

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

Typeclass Instances
-------------------

A typeclass instance of the [`Defer`](https://github.com/sjbiaga/kittens/blob/main/recursion-4-Defer/README.md) typeclass
asks for an `implicit` `F; Defer[F]` typeclass instance in scope. Given the `fa: => WriterT[F, L, A]` parameter, the method
`defer` is invoked with receiver `F` and argument `fa.run`. This argument uses `fa` which is a call-by-name parameter, but
the `defer` method is also passed a call-by-name argument, so `fa.run` will not be evaluated: the call-by-name flavor of the
`fa` parameter continues in the argument `fa.run`:

```Scala
implicit def ... (implicit F: Defer[F]): ... =
  new Defer[WriterT[F, L, *]] {
	def defer[A](fa: => WriterT[F, L, A]): WriterT[F, L, A] =
	  WriterT(F.defer(fa.run))
  }
```

Exercise 08.2
=============

Implement an `Expr`ession parser and builder that log the _operations_ used to create expressions. Also, implement an
evaluator that logs the _operators_ while the evaluation is ongoing. Show that the parser log and the evaluator log are
one-to-one. Use also "logged" `Expr`essions in the builder. Try to indent parenthesized `Expr`essions, too.

[Hint: each log is a `String` terminated by newline character `'\n'`. The "log", associated with a value, is a `String`,
hence the "prime" (`ʹ`) types `Writerʹ[T]`, `Exprʹ[T]` and `Doubleʹ`:

```Scala
type Writerʹ[T] = Writer[String, T]

type Exprʹ[T] = Writerʹ[Expr[T]]  // the `Parser` and builder base types

type Doubleʹ = Writer[String, Double]  // the return type of the evaluator
```

When logging a new message, while combining existing logs, a method `putʹ[T, U]` delegates to the method `putT[Id, String, T]`
from the companion object `WriterT`, and returns a `Writerʹ[T]`:

```Scala
def putʹ[T, U](valʹ: T)(log: Writerʹ[U]*)(msg: String): Writerʹ[T] =
  putT[Id, String, T](valʹ)(log.foldRight(msg)(_.swap.value + _) + "\n")
```

Its parameters are:

1. `valʹ: T` - the value to put in the `Writerʹ[T]` case class;

2. `log: Writerʹ[U]` - zero or more logs where to extract the `String` logs from and combine them into one;

3. `msg: String` - a new log message to append to existing logs, which is why `foldRight` is used to start appending to the
   last log and then combine them from right to left.

If messages should be indented, an implicit `indent` parameter can be used to prefix any message with the indentation (spaces
counting a multiple of _two_).

```Scala
def putʹ[T, U](valʹ: T)(log: Writerʹ[U]*)(msg: String)(implicit indent: String): Writerʹ[T] =
  putT[Id, String, T](valʹ)(log.foldRight(indent + msg)(_.swap.value + _) + "\n")
```

When there are no existing logs, the method `putʹ` should be adapted to:

```Scala
def putʹ[T](valʹ: T)(msg: String): Writerʹ[T] = putʹ(valʹ)()(msg)
```
An implicit `indent` parameter should be added for the indentation exercise as well.]

Solution - Part 1 - Parser
--------------------------

Recall the `Expr`ession `enum`eration with the cases:

1. unary - `Inv`, `Val`;

1. binary - `Add`, `Sub`, `Mul`, `Div`;

1. nullary - `Zero`, `One`:

```Scala
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
```

The companion object extends `JavaTokenParsers` in order to use the `parseAll` method and the`Parser` type; it hosts the
hint types and methods as well:

```Scala
object Expr extends JavaTokenParsers:

  type unit = Expr.Zero.type | Expr.One.type

  type Writerʹ[T] = Writer[String, T]

  type Exprʹ[T] = Writerʹ[Expr[T]]

  type Doubleʹ = Writer[String, Double]

  def putʹ[T, U](valʹ: T)(log: Writerʹ[U]*)(msg: String): Writerʹ[T] =
    putT[Id, String, T](valʹ)(log.foldRight(msg)(_.swap.value + _) + "\n")

  def putʹ[T](valʹ: T)(msg: String): Writerʹ[T] =
    putʹ(valʹ)()(msg)
```

We modify the type of the _parser_ to `Exprʹ[Int | Double]` - which is a writer -, and use `putʹ` to combine the logs for the
(left hand side and) right hand side, while appending a new message with the content corresponding to the parsed (unary or
binary) operator:

```Scala
  def expr(implicit unit: unit): Parser[Exprʹ[Int | Double]] =
    term ~ rep(("+"|"-") ~ term) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "+" ~ rhs) =>
          putʹ(Add(lhs.value, rhs.value))(lhs, rhs)("addition")
        case (lhs, "-" ~ rhs) =>
          putʹ(Sub(lhs.value, rhs.value))(lhs, rhs)("subtraction")
      }
    }

  def term(implicit unit: unit): Parser[Exprʹ[Int | Double]] =
    factor ~ rep(("*"|"/") ~ factor) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "*" ~ rhs) =>
          putʹ(Mul(lhs.value, rhs.value))(lhs, rhs)("multiplication")
        case (lhs, "/" ~ rhs) =>
          putʹ(Div(lhs.value, rhs.value))(lhs, rhs)("division")
      }
    }

  def factor(implicit unit: unit): Parser[Exprʹ[Int | Double]] =
    ("+"|"-") ~ literal ^^ {
      case "-" ~ rhs if unit eq Zero =>
        putʹ(Inv(rhs.value))(rhs)("unary negation")
      case "+" ~ rhs =>
        putʹ(Add(Zero, rhs.value))(rhs)("addition with zero")
      case "-" ~ rhs =>
        putʹ(Sub(Zero, rhs.value))(rhs)("subtraction from zero")
    } |
    literal

  def literal(implicit unit: unit): Parser[Exprʹ[Int | Double]] =
    floatingPointNumber ^^ {
      _.toDouble match
        case 0d => putʹ(Zero)("constant zero: Double")
        case 1d => putʹ(One)("constant one: Double")
        case n  => putʹ(Val(n))(s"value $n: Double")
    } |
    decimalNumber ^^ {
      _.toInt match
        case 0 => putʹ(Zero)("constant zero: Int")
        case 1 => putʹ(One)("constant one: Int")
        case n => putʹ(Val(n))(s"value $n: Int")
    } |
    "("~> expr(using unit) <~")" ^^ { _.tell("parentheses\n") }
```

There is no combination of logs for the nullary operators - because there are none existing. Also, an expression in
parentheses is logged using `WriterT#tell` method, _after_ it is parsed.

The only change to the interpolator is that of the return type, which is just added a prime.

```Scala
  implicit class ExprInterpolator(private val sc: StringContext) extends AnyVal:
    def x(args: Any*)(implicit unit: unit): Exprʹ[Int | Double] =
      val inp = (sc.parts zip (args :+ "")).foldLeft("") {
        case (r, (p, a)) => r + p + a
      }
      parseAll(expr, inp).get
```

Solution - Part 2 - Builder
---------------------------

For `swapping`, we use a function introduced in [Lesson 03 - Natural Transformations: Swapping the Additive with the Multiplicative](https://github.com/sjbiaga/kittens/blob/main/expr-03-swap/README.md#natural-transformations-swapping-the-additive-with-the-multiplicative),
but with a stack safe implementation:

```Scala
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
```

The builder is modified in the signatures of the "operator" methods (except `invert`) and in the methods `open` and `close`:

```Scala
  final case class Builder[T](lhs: Exprʹ[T], private var save: List[Exprʹ[T]]):
    private def fill(n: Int) = List.fill(0 max n)(())
    def swapping(implicit unit: unit) =
      Builder(putʹ(swap(lhs.value))(lhs)("swapping"), save)
    def add(rhs: Expr[T], n: Int = 1)(using m: String = "") =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              putʹ(Add(lhs.value, rhs))(lhs)(m + "adding")
          }
        , save
      )
    def subtract(rhs: Expr[T], n: Int = 1)(using m: String = "") =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              putʹ(Sub(lhs.value, rhs))(lhs)(m + "subtracting")
          }
        , save
      )
    def multiply(rhs: Expr[T], n: Int = 1)(using m: String = "") =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              putʹ(Mul(lhs.value, rhs))(lhs)(m + "multiplying")
          }
        , save
      )
    def divide(rhs: Expr[T], n: Int = 1)(using m: String = "") =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              putʹ(Div(lhs.value, rhs))(lhs)(m + "dividing")
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
    def close(f: (Builder[T], Expr[T]) => String ?=> Builder[T], invert: Int = 0) =
      val self = Builder(save.head, save.tail)
      f(self, lhs.value)(using putʹ(())(lhs)("closing").swap.value)
        .invert(invert)
  object Builder:
    def start[T] = From[T]("starting", Nil)
    final case class From[T](msg: String, save: List[Exprʹ[T]]):
      def apply(lhs: Expr[T]): Builder[T] =
        Builder(putʹ(lhs)(msg), save)
```

The extra parameter `m: String` is empty, except when its method is invoked from `close`, when it contains the log of the
right hand side, appended with the message "closing".

When a parenthesis is `open`ed, it starts from an `Expr`ession with a log of just one line: "opening"; the current value
_and_ the log are `save`d on a stack, while a new (nested) builder is instantiated.

Upon the invocation `f(self, lhs.value)` - in the `close` method - of a `Builder` "binary" method (in the form `_.add(_)`,
`_.subtract(_)`, `_.multiply(_)`, or `_.divide(_)`), the current log is appended the message "closing" and passed as
parameter `m` to the method.

If the parameter `n` to such method is 0, the former value will not be combined with the current value. Otherwise, if `n`is
greater than 1, the left hand side will transform into the accumulator of a `foldLeft` operation, where the right hand side
is always the same, and the current log `m` - when `close`ing - is repeated for each application of the operator.

Solution - Part 3 - Evaluator
-----------------------------

The return type of `eval` is a `Double` `Writerʹ` - or `Doubleʹ`. The messages describe operators, rather than operations, in
a simple manner, using the same `putʹ` method.

```Scala
  def eval(expr: Expr[Double])(implicit unit: unit): Doubleʹ =
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
```

Solution - Part 4 - Builder with log
------------------------------------

The following "prime" methods are added: `_.addʹ(_)`, `_.subtractʹ(_)`, `_.multiplyʹ(_)`, and `_.divideʹ(_)`, as well as
`openʹ` and `closeʹ`:

```Scala
  final case class Builder[T](lhs: Exprʹ[T], private var save: List[Exprʹ[T]]):
    private def fill(n: Int) = List.fill(0 max n)(())
    def swapping(implicit unit: unit) =
      Builder(putʹ(swap(lhs.value))(lhs)("swapping"), save)
    def add(rhs: Expr[T], n: Int = 1)(using m: String = "") =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              putʹ(Add(lhs.value, rhs))(lhs)(m + "adding")
          }
        , save
      )
    def addʹ(rhs: Exprʹ[T], n: Int = 1)(using m: String = "") =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              putʹ(Add(lhs.value, rhs.value))(lhs, rhs)(m + "adding")
          }
        , save
      )
    def subtract(rhs: Expr[T], n: Int = 1)(using m: String = "") =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              putʹ(Sub(lhs.value, rhs))(lhs)(m + "subtracting")
          }
        , save
      )
    def subtractʹ(rhs: Exprʹ[T], n: Int = 1)(using m: String = "") =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              putʹ(Sub(lhs.value, rhs.value))(lhs, rhs)(m + "subtracting")
          }
        , save
      )
    def multiply(rhs: Expr[T], n: Int = 1)(using m: String = "") =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              putʹ(Mul(lhs.value, rhs))(lhs)(m + "multiplying")
          }
        , save
      )
    def mutiplyʹ(rhs: Exprʹ[T], n: Int = 1)(using m: String = "") =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              putʹ(Mul(lhs.value, rhs.value))(lhs, rhs)(m + "multiplying")
          }
        , save
      )
    def divide(rhs: Expr[T], n: Int = 1)(using m: String = "") =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              putʹ(Div(lhs.value, rhs))(lhs)(m + "dividing")
          }
        , save
      )
    def divideʹ(rhs: Exprʹ[T], n: Int = 1)(using m: String = "") =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              putʹ(Div(lhs.value, rhs.value))(lhs, rhs)(m + "dividing")
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
    def close(f: (Builder[T], Expr[T]) => String ?=> Builder[T], invert: Int = 0) =
      val self = Builder(save.head, save.tail)
      f(self, lhs.value)(using putʹ(())(lhs)("closing").swap.value)
        .invert(invert)
    def closeʹ(f: (Builder[T], Exprʹ[T]) => String ?=> Builder[T], invert: Int = 0) =
      val self = Builder(save.head, save.tail)
      f(self, lhs)(using "closing\n")
        .invert(invert)
  object Builder:
    def start[T] = From[T]("starting", Nil)
    final case class From[T](msg: String, save: List[Exprʹ[T]]):
      def apply(lhs: Expr[T]): Builder[T] =
        Builder(putʹ(lhs)(msg), save)
      def apply(lhs: Exprʹ[T]): Builder[T] =
        Builder(putʹ(lhs.value)(lhs)(msg), save)
```

These prime methods allow _writers_ to be calculated with, too. There is a slight difference between the two closing methods,
`close` and `closeʹ`: the latter's only third `String` parameter is `"closing\n"`, because the log of the right hand side
(the current log) is combined in the callback method instead, e.g., `_.addʹ(_)`:

```Scala
    def addʹ(rhs: Exprʹ[T], n: Int = 1)(using m: String = "") =
      Builder (
        fill(n)
          .foldLeft(lhs) {
            (lhs, _) =>
              putʹ(Add(lhs.value, rhs.value))(lhs, rhs)(m + "adding")  // rhs contains the current log when closing
          }
        , save
      )
```

Solution - Part 5
-----------------

To show that parsing an expression and evaluating it write two logs that are one-to-one, we `split` each log in lines, filter
out lines containing `"parentheses"` from the former, and `zip` the two logs together:

```Scala
given unit = Zero

val x = x"(1.5+4-2)*3"

val (_, log) = x.listen.value
val (_, logʹ) = eval(x.value.asInstanceOf[Expr[Double]]).listen.value
var ls = log.split("\n")
val lsʹ = logʹ.split("\n")
ls = ls.filterNot(_ == "parentheses")
println(s"""zipped:\n${(ls zip lsʹ).mkString("\n")}""")
```

Solution - Part 6
-----------------

1. The writer types and methods in the companion object are the same, respectively, with an added implicit parameter `indent`:

```Scala
object Expr extends JavaTokenParsers:

  type unit = Expr.Zero.type | Expr.One.type

  type Writerʹ[T] = Writer[String, T]

  type Exprʹ[T] = Writerʹ[Expr[T]]

  type Doubleʹ = Writer[String, Double]

  def putʹ[T, U](valʹ: T)(log: Writerʹ[U]*)(msg: String)(implicit indent: String): Writerʹ[T] =
    putT[Id, String, T](valʹ)(log.foldRight(indent + msg)(_.swap.value + _) + "\n")

  def putʹ[T](valʹ: T)(msg: String)(implicit indent: String): Writerʹ[T] =
    putʹ(valʹ)()(msg)
```

2. The slight modifications to the parser are to add the implicit `indent` parameter, respectively, to increase the
   indentation for parenthesized expressions:

```Scala
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
    literal

  def literal(implicit unit: unit, indent: String): Parser[Exprʹ[Int | Double]] =
    floatingPointNumber ^^ {
      _.toDouble match
        case 0d => putʹ(Zero)("constant zero: Double")
        case 1d => putʹ(One)("constant one: Double")
        case n  => putʹ(Val(n))(s"value $n: Double")
    } |
    decimalNumber ^^ {
      _.toInt match
        case 0 => putʹ(Zero)("constant zero: Int")
        case 1 => putʹ(One)("constant one: Int")
        case n => putʹ(Val(n))(s"value $n: Int")
    } |
    "("~> expr(using unit, indent + "  ") <~")" ^^ { _.tell(s"${indent}parentheses\n") }
```

The log lines containing `"parentheses"` only _end with_ this `String`, instead of being equal to it.

3. The slight modification to the interpolator is to add the empty `String` as the initial indentation:

```Scala
  implicit class ExprInterpolator(private val sc: StringContext) extends AnyVal:
    def x(args: Any*)(implicit unit: unit): Exprʹ[Int | Double] =
      val inp = (sc.parts zip (args :+ "")).foldLeft("") {
        case (r, (p, a)) => r + p + a
      }
      parseAll(expr(using unit, ""), inp).get
```

4. There is a slight modification to the builder: because implicit `String`s are reserved to indentation, the right hand side
   current log when `close`ing is an `Option[String]` instead. The `swap` method remains the same. The logic of `open`ing and
   `close`ing is subtly changed. Thus, when a "parenthesis" is `open`ed, the indentation is increased by two, and decreased
   by two (`indent.substring(2)`) when a "parenthesis" is `close`d. The same observation as to prepending the current
   "right hand side" log when `close`ing, holds in the latter case, as concerning the case of `closeʹ`:

```Scala
  final case class Builder[T](lhs: Exprʹ[T], private var save: List[Exprʹ[T]])(implicit indent: String):
    def indent(rhs: Exprʹ[T]): Exprʹ[T] =
      rhs.mapWritten(_.split("\n").map(indent + _).mkString("", "\n", "\n"))
    private def fill(n: Int) = List.fill(0 max n)(())
    def swapping(implicit unit: unit) =
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
          implicit val indentʹ = if m eq None then indent else ""
          fill(n)
            .foldLeft(lhs) {
              (lhs, _) =>
                putʹ(Div(lhs.value, rhs))(lhs)(m.map(_ + indent + "dividing").getOrElse("dividing"))
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
      implicit val indentʹ = indent.substring(2)
      val self = Builder(save.head, save.tail)
      f(self, lhs.value)(using Some(putʹ(())(lhs)("closing").swap.value))
        .invert(invert)
    def closeʹ(f: (Builder[T], Exprʹ[T]) => Option[String] ?=> Builder[T], invert: Int = 0) =
      implicit val indentʹ = indent.substring(2)
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
```

However, there are two more clarifications to be made concerning the latter (`close`ing) case.

- In the case of the "non-prime" methods, on one hand, when `close`ing (i.e., parameter `m` _is not_ `None`), the current log
  lines are already indented, and _only_ the one line _immediately after_ the `"closing"` line need be indented - e.g., for
  `_.add(_)`:

```Scala
val indentʹ = if m eq None then indent else ""
putʹ(Add(lhs.value, rhs))(lhs)(m.map(_ + indent + "adding").getOrElse("adding"))(using indentʹ)
```

- In the case of the "prime" methods, on the other hand, when _not_ `close`ing (i.e., parameter `m` _is_ `None`), the right
  hand side log lines _are not_ indented, so both these _and_ the one message line need be indented - e.g., for `_.addʹ(_)`:

```Scala
val rhsʹ = if m eq None then indent(rhs) else rhs
putʹ(Add(lhs.value, rhsʹ.value))(lhs, rhsʹ)(m.map(_ + indent + "adding").getOrElse("adding"))
```

where the method `indent` is defined as:

```Scala
def indent(rhs: Exprʹ[T]): Exprʹ[T] =
  rhs.mapWritten(_.split("\n").map(indent + _).mkString("", "\n", "\n"))
```

Note that `mapWritten` is used, which changes (i.e., indents) only the log.

5. The slight modification to the evaluator is that an implicit _empty_ indentation must be defined in the scope of `evalʹ`.

```Scala
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
```

6. To show that parsing an expression and evaluating it write two logs that are one-to-one, the slight modification is that
   the log lines - filtered out - containing `"parentheses"` do _end with_ this `String`, instead of being equal to it.

```Scala
given unit = Zero

val x = x"(1.5+4-2)*3"

val (_, log) = x.listen.value
val (_, logʹ) = eval(x.value.asInstanceOf[Expr[Double]]).listen.value
var ls = log.split("\n")
val lsʹ = logʹ.split("\n")
ls = ls.filterNot(_.endsWith("parentheses"))
println(s"""zipped:\n${(ls zip lsʹ).mkString("\n")}""")
```

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-5-ReaderT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-7-StateT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)
