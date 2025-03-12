Lesson 03: A Rich Language of Expressions (cont'd)
==================================================

An `Expr`ession Parser (cont'd)
-------------------------------

In our former parser, an `expr`ession was a `term ~ ("+"|"-") ~ term`. This can handle only two terms; moreover, addition (or
subtraction) is left-associative, which that parser obviously did not capture.

The parser library has a `rep` combinator, which parses repetitions: in our case, zero or more operations:

```Scala
object Expr extends JavaTokenParsers:
  import Expr._
  def expr(implicit unit: unit): Parser[Expr[Int | Double]] =
    term ~ rep(("+"|"-") ~ term) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "+" ~ rhs) => Add(lhs, rhs)
        case (lhs, "-" ~ rhs) => Sub(lhs, rhs)
      }
    }
```

The main change is the parser `term ~ rep(("+"|"-") ~ term)`, which looks a lot like previous, but allows for any number of
left-associative additions or subtractions. The `expr` parser function folds a list of operators (plus or minus) and
operands, starting with the leftmost term.

What about unary negation? Unary minus (or plus) binds tighter, therefore they prefix the leaf/`literal` parser further
below.

A `term` is a repetition of left-associative multiplications or divisions:

```Scala
  def term(implicit unit: unit): Parser[Expr[Int | Double]] =
    factor ~ rep(("*"|"/") ~ factor) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "*" ~ rhs) => Mul(lhs, rhs)
        case (lhs, "/" ~ rhs) => Div(lhs, rhs)
      }
    }
```

Similarly, the `term` parser function folds a list of operators (times or divide) and operands, starting with the leftmost
term.

Next, a `factor` is simply a `literal`, possibly prefixed by unary plus or minus operators:

```Scala
  def factor(implicit unit: unit): Parser[Expr[Int | Double]] =
    ("+"|"-") ~ literal ^^ {
      case "-" ~ rhs if unit eq Zero => Inv(rhs)
      case "+" ~ rhs => Add(Zero, rhs)
      case "-" ~ rhs => Sub(Zero, rhs)
    } |
    literal ^^ { identity }
```

We may see that the `implicit` `unit` parameter is used here to _prevent_ turning a negated expression via `Inv` into a
subtraction via `Sub`; this is why all parser have this `implicit` parameter, though unused: it cannot be omitted, because of
the hierarchical way in which parsers depend on each other.

As [before](https://github.com/sjbiaga/kittens/blob/main/expr-04-parser/README.md), the literal parser is a method `literal`
of type `Parser[Expr[Int | Double]]`; it can be either a `decimalNumber` or a `floatingPointNumber`, or else specifically
(although not a literal per se) an `expr`ession in parentheses:

```Scala
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
```

[The `expr`ession in parentheses could have been a `factor`, but because of the unary operators, we want to be able to negate
an `expr`ession in parentheses as well.]

A `String` Interpolator for `Expr`essions
-----------------------------------------

We are now able to interpolate Scala `String`s using the `expr`ession parser. We choose "`x`" as method name, and follow the
general indications of implementing an interpolator: an `implicit` value `class` with a `StringContext` parameter, and one
method with arguments the interpolated values, i.e., either just prefixed with `$` or also between a pair of braces:

```Scala
  implicit class ExprInterpolator(private val sc: StringContext) extends AnyVal:
    def x(args: Any*)(implicit unit: unit): Expr[Int | Double] =
      val inp = (sc.parts zip (args :+ "")).foldLeft("") {
        case (r, (p, a)) => r + p + a
      }
      parseAll(expr, inp) match
        case Success(it, _) => it
```

The number of (constant) parts is always plus one the size of arguments: so, we fold the paired parts and arguments, with an
accumulator function that basically puts a part before the argument. Finally, we use `parseAll` with parameters, the `expr`
parser, and input - the concatenated parts and arguments.

We slightly modify the `swap` natural transformation to take into account the inverse of `Zero` if the `given` `unit` is
`One` (i.e., the multiplicative part is a semigroup with identity) and translate it as `Div`ision by `Zero`:

```Scala
 val swap: unit ?=> Expr ~> Expr =
  new (Expr ~> Expr):
    def apply[T](expr: Expr[T]): Expr[T] =
      expr match
        case Zero          => One
        case One           => Zero
        case Add(lhs, rhs) => Mul(apply(lhs), apply(rhs))
        case Sub(lhs, rhs) => Div(apply(lhs), apply(rhs))
        case Mul(lhs, rhs) => Add(apply(lhs), apply(rhs))
        case Div(lhs, rhs) => Sub(apply(lhs), apply(rhs))
        case Inv(Zero)
          if summon[unit] eq One => apply(Div(One, Zero))
        case Inv(rhs)      => Inv(apply(rhs))
        case it            => it
```

Thus, `given` `unit` is `One`, `Inv(Zero)` and `swap(swap(Inv(Zero)))` are no longer identical.

Here, `unit ?=>` means there is an implicit parameter of type `unit` that is always passed implicitly to `swap` in the body
of method `apply[T]`; such function type is specific to Scala 3 only.

[Next](https://github.com/sjbiaga/kittens/blob/main/expr-06-builder/README.md)

[Previous](https://github.com/sjbiaga/kittens/blob/main/expr-04-parser/README.md)
