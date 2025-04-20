[First](https://github.com/sjbiaga/kittens/blob/main/expr-01-trait/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/expr-03-swap/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-05-parser/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/expr-09-ring/README.md)

Lesson 03: A Rich Language of Expressions (cont'd)
==================================================

An `Expr`ession Parser
----------------------

Scala [parser combinators](https://github.com/scala/scala-parser-combinators) is a library for writing parsers. For `Expr`,
we will first develop a parser with some limitations, but elementary for the sake of simplicity. Expressions are made of
terms which are made of factors. In order to use (both decimal and floating point) numbers, the companion object `Expr` where
the parser methods are implemented extends the `scala.util.parsing.combinator.JavaTokenParsers` class.

So, let us start with expressions - the parser is a method `expr` of type `Parser[Expr[Int | Double]]`; we can add or
subtract two `term`s, negate one `term`, or neither - in which case an expression is just a `term`; operators map directly to
`Add` or `Sub`:

```Scala
import scala.util.parsing.combinator.JavaTokenParsers
object Expr extends JavaTokenParsers:
  import Expr._
  def expr: Parser[Expr[Int | Double]] =
    term ~ ("+"|"-") ~ term ^^ {
      case lhs ~ "+" ~ rhs => Add(lhs, rhs)
      case lhs ~ "-" ~ rhs => Sub(lhs, rhs)
    } |
    ("+"|"-") ~ term ^^ {
      case "+" ~ rhs => Add(Zero, rhs)
      case "-" ~ rhs => Sub(Zero, rhs)
    } |
    term ^^ { identity }
```

Note that because we inherit `JavaTokenParsers`, the type `Parser` is a visible nested class. Also, `p ^^ f` is short for
functor `map`ping (of `f` upon `Parser` functor `p`).

The term parser is a method `term` of type `Parser[Expr[Int | Double]]`; we can multiply or divide two `factor`s, or else a
`term` is just a `factor`; operators map directly to `Mul` or `Div`:

```Scala
  def term: Parser[Expr[Int | Double]] =
    factor ~ ("*"|"/") ~ factor ^^ {
      case lhs ~ "*" ~ rhs => Mul(lhs, rhs)
      case lhs ~ "/" ~ rhs => Div(lhs, rhs)
    } |
    factor ^^ { identity }
```

The factor parser is a method `factor` of type `Parser[Expr[Int | Double]]`; it can be either a `decimalNumber` or a
`floatingPointNumber`, or else an `expr`ession in parentheses. Numbers zero and one are intercepted and mapped to objects
`Zero`, respectively, `One`; else, a number - either `Int` or `Double` (hence the union type in the `Parser`) - is wrapped
in a `Val`.

```Scala
  def factor: Parser[Expr[Int | Double]] =
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

The `~>` combinator keeps only the _right_ result, while the `<~` combinator keeps only the _left_ result.

We can now parse (trivial) expressions:

```Scala
parseAll(expr, "2*5+7")
```

but should we try to add more terms than two:

```Scala
parseAll(expr, "2*5+7+1") // runtime error
```

we get an error. This is because our parser is weak: it can parse at most two terms with two factors each.

[First](https://github.com/sjbiaga/kittens/blob/main/expr-01-trait/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/expr-03-swap/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-05-parser/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/expr-09-ring/README.md)
