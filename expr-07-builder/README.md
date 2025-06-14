[First](https://github.com/sjbiaga/kittens/blob/main/expr-01-trait/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/expr-06-builder/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-CoflatMap/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/expr-09-ring/README.md)

Lesson 03: A Rich Language of Expressions (cont'd)
==================================================

An `Expr`ession Builder (cont'd)
--------------------------------

A more elaborated builder allows for a second `Int`eger parameter, that specifies how many operators with the same right hand
side operand should be generated. For this, `List.fill(0 max n)(rhs)` yields a list of size `n` with only occurrences of
`rhs`.

```Scala
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
```

The second parameter to `close` is an `Int`eger, specifying how many times the result of `f` should be inverted.

[First](https://github.com/sjbiaga/kittens/blob/main/expr-01-trait/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/expr-06-builder/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-CoflatMap/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/expr-09-ring/README.md)
