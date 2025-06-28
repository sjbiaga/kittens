[First](https://github.com/sjbiaga/kittens/blob/main/monoid-1-option/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/monoid-4-resolve/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md)

Lesson 05: Monoids (cont'd)
===========================

[Higher-Kinded `Monoid`s](https://typelevel.org/cats/nomenclature.html#monoidk)
-------------------------------------------------------------------------------

Because `Expr` has (higher) kind `* -> *`, it cannot have a typeclass instance of the `Monoid` typeclass. However,
independent of the base type,

1. we can form an `Expr`ession by `Add`ing or `Mul`tiplying two `Expr`essions, depending on which `unit` is given

1. we can use `Zero` or `One` - depending on which `unit` is given - as identity elements even at this higher level.

In `Cats`, this is a candidate for a typeclass instance of the `MonoidK` typeclass - a higher-kinded monoid:

```Scala
import cats.MonoidK

implicit def kittensExprMonoidK(implicit unit: unit): MonoidK[Expr] =
  new MonoidK[Expr]:
    def empty[A]: Expr[A] = unit
    def combineK[A](x: Expr[A], y: Expr[A]): Expr[A] =
      unit match
        case Zero => Add(x, y)
        case One  => Mul(x, y)
```

Via the
[builder for `Expr`essions](https://github.com/sjbiaga/kittens/blob/main/expr-07-builder/README.md#an-expression-builder-contd),
we can use two `Expr` operands at a higher combination level using the `<+>` rich wrapper method:

```scala
scala> import cats.syntax.semigroupk.*

scala> given unit = One
lazy val given_unit: unit

scala> Builder.start(x"0")
  .add(One)
  .multiply(Val(5d), 4)
    .open(One)
    .add(One, 2)
    .close(_.add(_))
  .lhs
val res0: Expr[Int | Double] = Inv(Add(Mul(Mul(Mul(Mul(Add(Zero,One),Val(5.0)),Val(5.0)),Val(5.0)),Val(5.0)),Add(Add(One,One),One)))

scala> Builder.start(x"0")
  .add(One)
  .multiply(Val(5d), 4)
    .open(One)
    .add(One, 2)
    .close(_.add(_))
  .swapping
  .lhs
val res1: Expr[Int | Double] = Inv(Mul(Add(Add(Add(Add(Mul(One,Zero),Val(5.0)),Val(5.0)),Val(5.0)),Val(5.0)),Mul(Mul(Zero,Zero),Zero)))

scala> res0 <+> res1
val res2: Expr[Int | Double] = Mul(Inv(Add(Mul(Mul(Mul(Mul(Add(Zero,One),Val(5.0)),Val(5.0)),Val(5.0)),Val(5.0)),Add(Add(One,One),One))),Inv(Mul(Add(Add(Add(Add(Mul(One,Zero),Val(5.0)),Val(5.0)),Val(5.0)),Val(5.0)),Mul(Mul(Zero,Zero),Zero))))
```

`MonoidK` inherits from `SemigroupK` which defines a method `algebra`, to obtain a semigroup for a certain base type - result
of kind `*`:

```scala
scala> given Monoid[Expr[Int | Double]] = MonoidK[Expr].algebra[Int | Double]
lazy val given_Monoid_Expr: cats.kernel.Monoid[Expr[Int | Double]]

scala> res0 |+| res1
val res3: Expr[Int | Double] = Mul(Inv(Add(Mul(Mul(Mul(Mul(Add(Zero,One),Val(5.0)),Val(5.0)),Val(5.0)),Val(5.0)),Add(Add(One,One),One))),Inv(Mul(Add(Add(Add(Add(Mul(One,Zero),Val(5.0)),Val(5.0)),Val(5.0)),Val(5.0)),Mul(Mul(Zero,Zero),Zero))))

scala> eval(res3)
val res4: Double = Infinity
```

[First](https://github.com/sjbiaga/kittens/blob/main/monoid-1-option/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/monoid-4-resolve/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md)
