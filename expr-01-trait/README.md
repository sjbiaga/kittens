Lesson 03: A Rich Language of Expressions
=========================================

We know from algebra that a [_ring_](https://en.wikipedia.org/wiki/Ring_(mathematics)) has an additive group and a
multiplicative semigroup with an identity element (or something like that); calling the latter a _unit_, we can implement in
Scala 3 a closed hierarchy of `enum` `case` classes in a purely functional (hence, immutable) manner:

```Scala
type unit = Expr.Zero.type | Expr.One.type
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

Above, depending on which "part" (additive or multiplicative) is the group and which the semigroup, we can have either `Zero`
or `One` be the identity element of the semigroup. This will matter when we handle division by zero, which is modelled by the
`Inv` `enum` `case`: if the unit is `One`, then `Inv(Zero)` - or Div(_, Zero) - will be the emblematic division by zero.

We know from [Lesson 01](https://github.com/sjbiaga/kittens/blob/main/covariant-1-contravariant/README.md) that `Expr` above
is covariant in the type parameter `T`: this allows for the objects `Zero` and `One` to extend `Expr[Nothing]` and be
assigned to whichever value of type `Expr[T]` is introduced.

Besides the `enum` `case`s for the additive and/or multiplicative operators, there is also the `enum` `case` `Val`, which
represents actual values (or "numbers").

Thus, we can form expressions such as

```Scala
Mul(Add(One, Zero), One)
```

or

```Scala
Mul(Add(One, Val(0)), Val(1)): Expr[Int]
```

[Next](https://github.com/sjbiaga/kittens/blob/main/expr-02-eval/README.md)

[Previous](https://github.com/sjbiaga/kittens/blob/main/queens-2-heap/README.md)
