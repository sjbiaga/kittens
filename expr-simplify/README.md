[Previous](https://github.com/sjbiaga/kittens/blob/main/queens-4-interpreter/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-paired/README.md)

Lesson 06: Natural Transformations (cont'd)
===========================================

Exercise 06.1
-------------

Implement a natural transformation `simplify: unit ?=> Expr ~> Expr` which simplifies `Expr`essions by removing the `Zero`s
and `One`s accordingly.

```scala
scala> simplify(Inv(Mul(Sub(One, Zero), Add(One, Zero))))
val res0: Expr[Nothing] = Inv(One)
```

Solution
--------

The pattern-matching is exactly as in the `swap` natural transformation, with the exception that these cases are preceded by
guarded cases, similar to the case, e.g., `Add(lhs, Zero)`, when the result is `apply(lhs)`. For `Sub(Zero, rhs)` the result
is `Inv(apply(rhs))` if the `unit` is `Zero`; for `Div(One, rhs)` the result is `Inv(apply(rhs))` if the `unit` is `One`. Of
course, we `apply` the natural transformation in the guards and test for `eq`uality with `Zero` or `One`:

```Scala
val simplify: unit ?=> Expr ~> Expr =
  new (Expr ~> Expr):
    val unit = summon[unit]
    def apply[T](expr: Expr[T]): Expr[T] =
      expr match
        case Add(lhs, rhs) if apply(rhs) eq Zero => apply(lhs)
        case Add(lhs, rhs) if apply(lhs) eq Zero => apply(rhs)
        case Sub(lhs, rhs) if apply(rhs) eq Zero => apply(lhs)
        case Sub(lhs, rhs) if (apply(lhs) eq Zero) && (unit eq Zero) => Inv(apply(rhs))
        case Mul(lhs, rhs) if apply(rhs) eq One => apply(lhs)
        case Mul(lhs, rhs) if apply(lhs) eq One => apply(rhs)
        case Mul(lhs, _) if apply(lhs) eq Zero => Zero
        case Mul(_, rhs) if apply(rhs) eq Zero => Zero
        case Div(lhs, rhs) if apply(rhs) eq One => apply(lhs)
        case Div(lhs, rhs) if (apply(lhs) eq One) && (unit eq One) => Inv(apply(rhs))
        case Div(lhs, rhs) if apply(lhs) eq Zero => Zero
        case Add(lhs, rhs) => Add(apply(lhs), apply(rhs))
        case Sub(lhs, rhs) => Sub(apply(lhs), apply(rhs))
        case Mul(lhs, rhs) => Mul(apply(lhs), apply(rhs))
        case Div(lhs, rhs) => Div(apply(lhs), apply(rhs))
        case Inv(rhs) => Inv(apply(rhs))
        case it => it

```

[Previous](https://github.com/sjbiaga/kittens/blob/main/queens-4-interpreter/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-paired/README.md)
