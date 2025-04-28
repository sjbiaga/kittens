[First](https://github.com/sjbiaga/kittens/blob/main/expr-01-trait/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/expr-05-parser/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-07-builder/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/expr-09-ring/README.md)

Lesson 03: A Rich Language of Expressions (cont'd)
==================================================

We mentioned [there](https://github.com/sjbiaga/kittens/blob/main/expr-02-eval/README.md) that instances of `enum` `case`
classes are the low-level instructions of a program. Here, we present a higher-level language of expressions, in a _fluent_
style.

An `Expr`ession Builder
-----------------------

We may apply the _builder_ design pattern to build an `Expr`ession using a more natural language, without mnemonics:

```Scala
final case class Builder[T](private val lhs: Expr[T], private var save: List[Expr[T]]):
  def build: Expr[T] = lhs
  def swapping(implicit unit: unit): Builder[T] = Builder(swap(lhs), save)
  def add(rhs: Expr[T]): Builder[T] = Builder(Add(lhs, rhs), save)
  def subtract(rhs: Expr[T]): Builder[T] = Builder(Sub(lhs, rhs), save)
  def multiply(rhs: Expr[T]): Builder[T] = Builder(Mul(lhs, rhs), save)
  def divide(rhs: Expr[T]): Builder[T] = Builder(Div(lhs, rhs), save)
  def invert: Builder[T] = Builder(Inv(lhs), save)
  def open: Builder.From[T] = Builder.From(build :: save)
  def close(f: (Builder[T], Expr[T]) => Builder[T], invert: Boolean = false): Builder[T] =
    val self = Builder(save.head, save.tail)
    if invert then f(self, lhs).invert
    else f(self, lhs)
object Builder:
  def start[T] = From[T](Nil)
  final case class From[T](save: List[Expr[T]]):
    def apply(lhs: Expr[T]): Builder[T] = Builder(lhs, save)
```

Each method of the `Builder[T]` `case` `class` has the same return type, the very same `Builder[T]` `case` `class`. The
parameter (except for `build`, `open` and `close` methods) is an `Expr[T]` - the right hands side operand of the
corresponding operator (`add` corresponds to `Add`, `multiply` to `Mul`, and so on).

For example, the following code:

```Scala
Builder.start(x"0")
  .add(One)
  .multiply(Val(5d))
    .open(One)
    .add(One)
    .close(_.add(_))
  .build
```

yields `Add(Mul(Add(Zero, One), Val(5.0)), Add(One, One))`, and corresponds to the expression "`(0 + 1) * 5.0 + (1 + 1)`".
Note that while the first pair of parentheses is not explicit, the second results from `open`ing and `close`ing a pair of
parentheses.

The argument to `close` is a method with a `Builder[T]` receiver and one parameter, such as `_.add(_)` or `_.divide(_)`.
Obviously, `invert` cannot fit this type, so a second `Boolean` parameter to `close` is used to `invert` the parenthesized
expresssion, if set to `true`.

The resulting value - however long - is stored in the heap of `JVM`. The code that builds it is just a language that is
evaluated by the `JVM`. Such a language can be even as tiny as two verbs, like `flatMap` and `map` methods used by Scala to
translate `for`-comprehensions (although there may also be a third - `withFilter`).

[First](https://github.com/sjbiaga/kittens/blob/main/expr-01-trait/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/expr-05-parser/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-07-builder/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/expr-09-ring/README.md)
