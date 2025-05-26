[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-6-WriterT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

[`ReaderT`](https://typelevel.org/cats/nomenclature.html#kleisli-or-readert)
----------------------------------------------------------------------------

`ReaderT` is actually a type alias for [`Kleisli`](https://typelevel.org/cats/datatypes/kleisli.html), whereas `Reader` is
`ReaderT` with `Id` for `F`:

```Scala
package cats

type ReaderT[F[_], -A, B] = Kleisli[F, A, B]

type Reader[-A, B] = ReaderT[Id, A, B]
```

`Kleisli` is a wrapper `case class` around a Kleisli arrow `A => F[B]`:

```Scala
final case class Kleisli[F[_], -A, B](run: A => F[B]) { self =>
  ...
}
```

It is of no coincidence that composition - the `andThen` method - with another Kleisli arrow `B => F[C]`, is an alias for the
`flatMapF` method, in terms of which also the `flatMap` method - the pillar of `for`-comprehensions - can be implemented,
where in all three cases an `implicit` typeclass instance `FlatMap[F]` must be in scope: either nesting `flatMap`s in the
translation of a `for`-comprehension, or chaining with `andThen`, the result of composing `Kleisli` objects is the same.

Note that in the results of these methods - of type `Kleisli[F, A, *]` - the type parameter `A` remains quasi the same (or
narrower), with the exception of the `dimap`, `local`, and `compose` methods. It is then to be expected that the result of
many methods starts with `Kleisli { a => ... }`, where the ellipses applies `run` to `a` (at some point), unless the Kleisli
arrow can be written neater as a composition of functions (via `andThen`).

Methods à la `map` or `flatMap`
-------------------------------

The `map` method resorts to `mapF`, which allows also for a change of context, from `F[_]` to `G[_]`, without imposing any
context bounds to the type constructor parameter `G[_]`: `run andThen f` is the Kleisli arrow of the result.

```Scala
def map[C](f: B => C)(implicit F: Functor[F]): Kleisli[F, A, C] =
  mapF(F.lift(f): F[B] => F[C])

def mapF[G[_], C](f: F[B] => G[C]): Kleisli[G, A, C] =
  Kleisli(run andThen f)
```

The `mapFilter` method has a function parameter which returns `Option[C]`, so a composition similar as before is the Kleisli
arrow of the result, except `FunctorFilter#liftFF` is used rather than `Functor#lift`:

```Scala
def mapFilter[C](f: B => Option[C])(implicit F: FunctorFilter[F]): Kleisli[F, A, C] =
  Kleisli(run andThen F.liftFF(f))
```

Because all the `Kleisli` objects in a `for`-comprehension share the same type parameter `A`, it is important to "bring" the
"particular" `Kleisli` objects - with different `A`s - into sharing the same `C` as the source type parameter of each Kleisli
arrow:

```Scala
def local[C](f: C => A): Kleisli[F, C, B] =
  Kleisli(run.compose(f))
```

that usually involves a common `C` `case class` from which other `A`s can be "projected". The `local` method (also known as
"contramap") first applies the "projection" `f`, and then continues by invoking `run` "locally", thus achieving two goals.

The `local` and `map` methods can be combined into a single method, known as `dimap`:

```Scala
def dimap[C, D](f: C => A)(g: B => D)(implicit F: Functor[F]): Kleisli[F, C, D] =
  Kleisli(f andThen run andThen F.lift(g))
```

The `flatMap` method resorts to `flatMapF`:

```Scala
def flatMap[AA <: A, C](f: B => Kleisli[F, AA, C])(implicit F: FlatMap[F]): Kleisli[F, AA, C] =
  Kleisli { a =>
    flatMapF(f(_).run(a)).run(a)
  }

def flatMapF[C](f: B => F[C])(implicit F: FlatMap[F]): Kleisli[F, A, C] =
  Kleisli(run andThen F.liftFM(f))
```

where `liftFM` is defined in the `FlatMap[F[_]]` trait:

```Scala
def liftFM[A, B](f: A => F[B]): F[A] => F[B] = flatMap(_)(f)
```

Let us rewrite `Kleisli#flatMapF` similar with `Kleisli#map` (using `F.lift`):

```Scala
def flatMapF[C](f: B => F[C])(implicit F: FlatMap[F]): Kleisli[F, A, C] =
  Kleisli { run andThen F.lift(f) andThen F.flatten }
```

All the difference is that we have to end by invoking `F.flatten`, because the return type of `f` is lifted in `F`. So we
just `map` the function `f` and we are half way there. In this light, we can implement `Kleisli#flatMap` without invoking
`Kleisli#flatMapF`:

```Scala
def flatMap[AA <: A, C](f: B => Kleisli[F, AA, C])(implicit F: FlatMap[F]): Kleisli[F, AA, C] =
  Kleisli { a =>
    val g: B => F[C] = f(_).run(a)
    val h: A => F[C] = run andThen F.lift(g) andThen F.flatten
    h(a)
  }
```

Now we can see that the order of functions that enter the composition via `andThen` is the same with `map`'s: first `run` and
then `f(_).run(a)`; and, specifically, `F.flatten`. Let us make explicit the arguments by applying the composition to `a: A`:

```Scala
def flatMap[AA <: A, C](f: B => Kleisli[F, AA, C])(implicit F: FlatMap[F]): Kleisli[F, AA, C] =
  Kleisli { (a: A) =>
    val fb: F[B] = this.run(a)
    val ffc: F[F[C]] = F.map(fb) { (b: B) =>
      val fc: F[C] = f(b).run(a)
      fc
    }
    val fc: F[C] = F.flatten(ffc)
    fc
  }
```

A lot of things seem to happen now. Yet, basically, there are two _pair of braces_, the _outer_ one and the _inner_ one. The
outer one maps an `A`, whereas the inner one handles a `B`. However, both apply `a: A`: the difference is that the outer
`run` is invoked with `this` as receiver, while the inner `run` is invoked with `f(b)` as receiver. For the latter invocation
succeeding the former, we need a `b`, that is unwrapped by the typeclass instance `F` from `fb` - the result of the former.

The inner block is handled by the `F[_]` context, which is why the result of `F.map` is _doubly_ inflated: _refactoring_, let
us replace `map` with `flatMap`:

```Scala
def flatMap[AA <: A, C](f: B => Kleisli[F, AA, C])(implicit F: FlatMap[F]): Kleisli[F, AA, C] =
  Kleisli { (a: A) =>
    val fb: F[B] = this.run(a)
    val fc: F[C] = F.flatMap(fb) { (b: B) =>
      val fc: F[C] = f(b).run(a)
      fc
    }
    fc
  }
```

Obviously, the two `fc`'s have the same type, but are not necessarily the same value. Now, let us try to remove the
_intermediary_ values:

```Scala
def flatMap[AA <: A, C](f: B => Kleisli[F, AA, C])(implicit F: FlatMap[F]): Kleisli[F, AA, C] =
  Kleisli { a => F.flatMap(this.run(a))(f(_).run(a)) }
```

and further let us use `Cats`' `flatMap` _syntax_:

```Scala
import cats.syntax.flatMap.*

def flatMap[AA <: A, C](f: B => Kleisli[F, AA, C])(implicit F: FlatMap[F]): Kleisli[F, AA, C] =
  Kleisli { a => this.run(a).flatMap(f(_).run(a)) }
```

or, introducing `g` again:

```Scala
import cats.syntax.flatMap.*

def flatMap[AA <: A, C](f: B => Kleisli[F, AA, C])(implicit F: FlatMap[F]): Kleisli[F, AA, C] =
  Kleisli { a =>
    val g: B => F[C] = f(_).run(a)
    this.run(a).flatMap(g)
  }
```

Now we can see that the actual invocation of `Kleisli#flatMap` - which is `this.flatMap(f)` - is _reflected_ at the
implementation level as `this.run(a).flatMap(g)`, where both `run: A => F[B]` and `g: B => F[C]` are Kleisli arrows: hence,
this implementation is identical in form with the composition of Kleisli arrows `run(_).flatMap(g)` applied to `a` - as
mentioned in [Exercise 04.1](https://github.com/sjbiaga/kittens/blob/main/kleisli-2-trampoline/README.md#exercise-041) for
the `Trampoline` monad. As can be seen, once we have an `a: A`, we have both `run(a): F[B]` and `g: B => F[C]`, which - via
`F.flatMap` - gives us an `F[C]`; and, both outer `F[B]` and inner `F[C]` result from applying `a: A`, in this order.

```Scala
def tap[AA <: A](implicit F: Functor[F]): Kleisli[F, AA, AA] =
  tapWith((a, _) => a)

def tapWith[C, AA <: A](f: (AA, B) => C)(implicit F: Functor[F]): Kleisli[F, AA, C] =
  Kleisli(a => F.map(run(a))(f(a, _)))

def tapWithF[C, AA <: A](f: (AA, B) => F[C])(implicit F: FlatMap[F]): Kleisli[F, AA, C] =
  Kleisli(a => F.flatMap(run(a))(f(a, _)))
```

Composing methods
-----------------

```Scala
def andThen[C](f: B => F[C])(implicit F: FlatMap[F]): Kleisli[F, A, C] =
  flatMapF(f)

def andThen[C](k: Kleisli[F, B, C])(implicit F: FlatMap[F]): Kleisli[F, A, C] =
  this.andThen(k.run)

def compose[Z, AA <: A](f: Z => F[AA])(implicit F: FlatMap[F]): Kleisli[F, Z, B] =
  Kleisli.shift(f andThen F.liftFM(run))

def compose[Z, AA <: A](k: Kleisli[F, Z, AA])(implicit F: FlatMap[F]): Kleisli[F, Z, B] =
  k.andThen(this)
```

Other methods
-------------

```Scala
def ap[C, D, AA <: A](f: Kleisli[F, AA, C])(implicit F: Apply[F], ev: B As (C => D)): Kleisli[F, AA, D] = {
  Kleisli { a =>
	val fb: F[C => D] = F.map(run(a))(ev.coerce)
	val fc: F[C] = f.run(a)
	F.ap(fb)(fc)
  }
}
```

```Scala
def apply(a: A): F[B] =
  run(a)
```

```Scala
def lift[G[_]](implicit G: Applicative[G]): Kleisli[λ[α => G[F[α]]], A, B] =
  mapF[λ[α => G[F[α]]], B](G.pure)
```

```Scala
def mapK[G[_]](f: F ~> G): Kleisli[G, A, B] =
  mapF(f.apply)
```

```Scala
def traverse[G[_], AA <: A](f: G[AA])(implicit F: Applicative[F], G: Traverse[G]): F[G[B]] =
  G.traverse(f)(run)
```

Methods from the companion object
---------------------------------

```Scala
def liftF[F[_], A, B](x: F[B]): Kleisli[F, A, B] =
  Kleisli(StrictConstFunction1(x))

def liftK[F[_], A]: F ~> Kleisli[F, A, *] =
  new (F ~> Kleisli[F, A, *]) { def apply[B](fb: F[B]): Kleisli[F, A, B] = Kleisli.liftF(fb) }

def pure[F[_], A, B](x: B)(implicit F: Applicative[F]): Kleisli[F, A, B] =
  liftF(F.pure(x))

def ask[F[_], A](implicit F: Applicative[F]): Kleisli[F, A, A] =
  Kleisli(F.pure)

def local[M[_], A, R](f: R => R)(fa: Kleisli[M, R, A]): Kleisli[M, R, A] =
  fa.local(f)

def fromFunction[M[_], R, A](f: R => A)(implicit M: Applicative[M]): Kleisli[M, R, A] =
  Kleisli(f andThen M.pure)
```

Typeclass Instances
-------------------

A typeclass instance of the [`Defer`](https://github.com/sjbiaga/kittens/blob/main/recursion-4-Defer/README.md) typeclass
asks for an `implicit` `F; Defer[F]` typeclass instance in scope. Given the `fa: => Kleisli[F, A, B]` parameter, the method
`defer` is invoked with receiver `F` and argument `cacheFa.run(a)`, where `a: A`. This argument uses `cacheFa` which is a
`lazy` `val`ue designed to evaluate the `fa` call-by-name parameter only once. But the `defer` method is also passed a
call-by-name argument, so `cacheFa.run(a)` will not be evaluated: the call-by-name flavor of the `fa` parameter continues in
the argument `cacheFa.run(a)`:

```Scala
implicit def ... (implicit F: Defer[F]): ... =
  new Defer[Kleisli[F, A, *]] {
	def defer[B](fa: => Kleisli[F, A, B]): Kleisli[F, A, B] = {
	  lazy val cacheFa = fa
	  Kleisli[F, A, B] { a =>
		F.defer(cacheFa.run(a))
	  }
	}
  }
```

Exercise 08.1
=============

In the lines of [this builder](https://github.com/sjbiaga/kittens/tree/main/expr-07-builder#an-expression-builder-contd) for
`Expr`essions, implement a _new_ builder that is based on the type:

```Scala
import cats.data.Reader

type Exprʹ[T] = Reader[String, Expr[T]]
```

where each operation uses `Kleisli#map` to obtain the result from the current left hand side (`Exprʹ[T]`) and a right hand
side parameter (`Expr[T]`). Only upon invoking `Builder#build` should a `String` be passed to `Kleisli#run`. `Builder#close`
must invoke `Builder#build`, so its signature must be prepended a first parameter list with just one `String` parameter too.
Likewise, add methods ("`add`", "`subtract`", "`multiply`", "`divide`") that take a `String` parameter and `build` the left
hand side operand from it, while the right hand side is an implicit `Exprʹ[T]` parameter where to inject the dependency.

The `Exprʹ[T]` implicits could involve
[this parser](https://github.com/sjbiaga/kittens/blob/main/expr-05-parser/README.md#an-expression-parser-contd), but the
choice of the parser must be free (only a `String` is the dependency of the builder):

```Scala
import cats.data.Reader

import Expr._

type Exprʹ[T] = Reader[String, Expr[T]]

given unit = Zero

given Exprʹ[Double] = Reader(???)

Builder.start
  .add(One)
  .inject("2 - 2")(_.subtract(_))
  .multiply(Val(5d), 4)
    .open
    .add(One, 2)
    .close("7 / 5")(_.add(_))
  .build("(1-0) * (1+0)")
```

Also, implement another parser, for example using [`cats-parse`](https://typelevel.org/cats-parse), and show that the same
builder can be used with different parsers. For identical built `Expr`essions, measure the time with one parser or another.

Until now, only `Kleisli#map` was involved: try to find a use case for `Kleisli#flatMap` as well.

[Hint: define `Expr`essions and their evaluator as follows:

```Scala
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
```

For the last part, use a `for`-comprehension with two identical readers (`lhs` and `rhs`) built by invoking `Builder#lhs`,
yielding `Div(lhs, rhs)`, so that `eval`uating results is `1` - indifferent of which dependency is injected.]

Solution - Part 1
-----------------

The [first parser](https://github.com/scala/scala-parser-combinators) is:

```Scala
import scala.util.parsing.combinator.JavaTokenParsers

object Exprʹ extends JavaTokenParsers:

  import Expr._

  def expr(implicit unit: unit): Parser[Expr[Double]] =
    term ~ rep(("+"|"-") ~ term) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "+" ~ rhs) => Add(lhs, rhs)
        case (lhs, "-" ~ rhs) => Sub(lhs, rhs)
      }
    }

  def term(implicit unit: unit): Parser[Expr[Double]] =
    factor ~ rep(("*"|"/") ~ factor) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "*" ~ rhs) => Mul(lhs, rhs)
        case (lhs, "/" ~ rhs) => Div(lhs, rhs)
      }
    }

  def factor(implicit unit: unit): Parser[Expr[Double]] =
    ("+"|"-") ~ literal ^^ {
      case "-" ~ rhs if unit eq Zero => Inv(rhs)
      case "+" ~ rhs => Add(Zero, rhs)
      case "-" ~ rhs => Sub(Zero, rhs)
    } |
    literal

  def literal(implicit unit: unit): Parser[Expr[Double]] =
    floatingPointNumber ^^ {
      _.toDouble match
        case 0d => Zero
        case 1d => One
        case n => Val(n)
    } |
    "("~> expr <~")"

  implicit class ExprInterpolator(private val sc: StringContext) extends AnyVal:
    def x(args: Any*)(implicit unit: unit): Expr[Double] =
      val inp = (sc.parts zip (args :+ "")).foldLeft("") {
        case (r, (p, a)) => r + p + a
      }
      parseAll(expr, inp).get
```

Solution - Part 2
-----------------

The [second parser](https://typelevel.org/cats-parse) is:

```Scala
import cats.parse.Parser
import cats.parse.{ Parser, Parser0, Numbers }
import Parser.{ charIn, defer, end }
import Numbers.jsonNumber

object Exprʹʹ:

  import Expr._

  private val whitespace: Parser[Unit] = charIn(" \t\r\n").void
  private val whitespaces0: Parser0[Unit] = whitespace.rep0.void

  private def char(cs: Char*): Parser[Char] = charIn(cs).surroundedBy(whitespaces0)

  def expr(implicit unit: unit): Parser[Expr[Double]] =
    (term ~ (char('+', '-') ~ term).rep0).map {
      case (lhs, rhs) => rhs.foldLeft(lhs) {
        case (lhs, ('+', rhs)) => Add(lhs, rhs)
        case (lhs, ('-', rhs)) => Sub(lhs, rhs)
      }
    }

  def term(implicit unit: unit): Parser[Expr[Double]] =
    (factor ~ (char('*', '/') ~ factor).rep0).map {
      case (lhs, rhs) => rhs.foldLeft(lhs) {
        case (lhs, ('*', rhs)) => Mul(lhs, rhs)
        case (lhs, ('/', rhs)) => Div(lhs, rhs)
      }
    }

  def factor(implicit unit: unit): Parser[Expr[Double]] =
    (char('+', '-') ~ literal).map {
      case ('-', rhs) if unit eq Zero => Inv(rhs)
      case ('+', rhs) => Add(Zero, rhs)
      case ('-', rhs) => Sub(Zero, rhs)
    } |
    literal

  def literal(implicit unit: unit): Parser[Expr[Double]] =
    jsonNumber.surroundedBy(whitespaces0).map {
      _.toDouble match
        case 0d => Zero
        case 1d => One
        case n => Val(n)
    } |
    char('(') *> defer(expr) <* char(')')

  def parserExpr(implicit unit: unit): Parser[Expr[Double]] = whitespaces0.with1 *> expr <* (whitespaces0 ~ end)

  implicit class ExprInterpolator(private val sc: StringContext) extends AnyVal:
    def x(args: Any*)(implicit unit: unit): Expr[Double] =
      val inp = (sc.parts zip (args :+ "")).foldLeft("") {
        case (r, (p, a)) => r + p + a
      }
      parserExpr.parseAll(inp).right.get
```

Solution - Part 3
-----------------

The `Builder` maintains the left hand side (`lhs`) as a `Reader` of type `Exprʹ[T]`, and with each operation (corresponding
to `case class` `<Op>`, e.g., `Add`) with a right hand side parameter (`rhs`) of type `Expr[T]`, it returns a new `Builder`
from the new left hand side that results as `lhs.map(<Op>(_, rhs))`:

```Scala
import cats.data.Reader

import Expr._

type Exprʹ[T] = Reader[String, Expr[T]]

final case class Builder[T](lhs: Exprʹ[T], private var save: List[Exprʹ[T]]):
  def build(x: String): Expr[T] = lhs.run(x)
  def fill(n: Int) = List.fill(0 max n)(())
  def add(rhs: Expr[T], n: Int = 1) =
    Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Add(_, rhs)) }, save)
  def add(x: String)(using rhs: Exprʹ[T]) =
    Builder(rhs.map(Add(build(x), _)), save)
  def subtract(rhs: Expr[T], n: Int = 1) =
    Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Sub(_, rhs)) }, save)
  def subtract(x: String)(using rhs: Exprʹ[T]) =
    Builder(rhs.map(Sub(build(x), _)), save)
  def multiply(rhs: Expr[T], n: Int = 1) =
    Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Mul(_, rhs)) }, save)
  def multiply(x: String)(using rhs: Exprʹ[T]) =
    Builder(rhs.map(Mul(build(x), _)), save)
  def divide(rhs: Expr[T], n: Int = 1) =
    Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Div(_, rhs)) }, save)
  def divide(x: String)(using rhs: Exprʹ[T]) =
    Builder(rhs.map(Div(build(x), _)), save)
  def invert(n: Int = 1): Builder[T] =
    Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Inv(_)) }, save)
  def inject(x: String)(f: (Builder[T], String) => Exprʹ[T] ?=> Builder[T])(using Exprʹ[T]) =
    f(this, x)
  def open(using lhs: Exprʹ[T]) = Builder(lhs, this.lhs :: save)
  def close(x: String)(f: (Builder[T], Expr[T]) => Builder[T], invert: Int = 0) =
    require(save.nonEmpty)
    val self = Builder(save.head, save.tail)
    f(self, build(x)).invert(invert)
object Builder:
  def start[T](using lhs: Exprʹ[T]) = Builder(lhs, Nil)
```

There are also operation methods which inject a dependency `String`, then continue with an implicit `Reader`, commencing as
right hand side. The `inject` method makes this obvious, by invoking the mentioned operations indirectly.

Solution - Part 4
-----------------

To measure time, we implement a method `elapsed` time between two timestamps:

```Scala
def elapsedʹ(start: Long, end: Long): (Long, Long, Long, Long) =
  val ms = (end - start) % 1000.0
  val ss = (end - start) / 1000.0
  val mm = ss / 60
  val hh = mm / 60
  (hh.toInt, (mm % 60).toInt, (ss % 60).toInt, ms.toInt)

def elapsed(start: Long, end: Long): String =
  val (hh, mm, ss, ms) = elapsedʹ(start, end)
  s"$hh:$mm:$ss.$ms"
```

Finally, our user code is the following:

```Scala
import alleycats.{ Zero => `0`, One => `1` }

given unit = Zero

given `0`[Double] = `0`(0d)
given `1`[Double] = `1`(1d)

{
  import Exprʹ._

  val start = System.currentTimeMillis

  given Exprʹ[Double] = Reader(parseAll(expr, _).get)

  val x = Builder.start
    .add(One)
    .inject("2 - 2")(_.subtract(_))
    .multiply(Val(5d), 4)
      .open
      .add(One, 2)
      .close("7 / 5")(_.add(_))
    .build("(1 - 0) * (1 + 0)")

  val end = System.currentTimeMillis

  println(s"${elapsed(start, end)} $x ${eval(x)}")
}

{
  import Exprʹʹ._

  val start = System.currentTimeMillis

  given Exprʹ[Double] = Reader(parserExpr.parseAll(_).right.get)

  val x = Builder.start
    .add(One)
    .inject("2 - 2")(_.subtract(_))
    .multiply(Val(5d), 4)
      .open
      .add(One, 2)
      .close("7 / 5")(_.add(_))
    .build("(1 - 0) * (1 + 0)")

  val end = System.currentTimeMillis

  println(s"${elapsed(start, end)} $x ${eval(x)}")
}
```

Solution - Part 5
-----------------

`Kleisli#flatMap` is involved when at least two generators are used in a `for`-comprehension. So, we can repeat those from
Part 4, lest the invocation to `Buidler#build` - instead, we return `Builder#lhs`:

```Scala
{
  val start = System.currentTimeMillis

  val r =
    for
      lhs <- {
        import Exprʹ._

        given Exprʹ[Double] = Reader(parseAll(expr, _).get)

        Builder.start
          .add(One)
          .inject("2 - 2")(_.subtract(_))
          .multiply(Val(5d), 4)
            .open
            .add(One, 2)
            .close("7 / 5")(_.add(_))
          .lhs
      }
      rhs <- {
        import Exprʹʹ._

        given Exprʹ[Double] = Reader(parserExpr.parseAll(_).right.get)

        Builder.start
          .add(One)
          .inject("2 - 2")(_.subtract(_))
          .multiply(Val(5d), 4)
            .open
            .add(One, 2)
            .close("7 / 5")(_.add(_))
          .lhs
      }
    yield
      Div(lhs, rhs)

  val x = r("(1 - 0) * (1 + 0)")

  val end = System.currentTimeMillis

  println(s"${elapsed(start, end)} $x ${eval(x)}")
}
```

Both the first and second generators correspond to `Kleisli`s which are injected the same dependency. Thus, being the same
built readers, the top-level `Div` operator will return `1` when evaluating the `x` expression.

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-6-WriterT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)
