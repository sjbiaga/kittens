Lesson 03: A Rich Language of Expressions (cont'd)
==================================================

Exercise 03.2
-------------

Combine the specification of method `eval` in
[Evaluation of Expressions](https://github.com/sjbiaga/kittens/blob/main/expr-02-eval/README.md) with the concept behind
`swap` from
[Natural Transformations: Swapping the Additive with the Multiplicative](https://github.com/sjbiaga/kittens/blob/main/expr-03-swap/README.md)
to design a _natural transformation_ from `Expr` to `Id` which evaluates an `Expr`ession in a `DivisionRing` typeclass.
Hint: implement the following trait instead of `Cats`' `FunctionK`.

```Scala
trait FunctionKʹ[R[_], F[_], G[_]]:
  def apply[A: R](fa: F[A]): G[A]
```

Note that `R[_]` in `FunctionKʹ[R[_], F[_], G[_]]` is a context bound.

Solution
--------

First, define a typeclass instance of `DivisionRing` for `Double`:

```Scala
implicit val kittensDoubleRing: Ring[Double] =
  new DivisionRing[Double]:
    override val zero = 0d
    override val one = 1d
    override def negate(n: Double) = 0d - n
    override def reciprocal(n: Double) = 1d / n
    override def plus(m: Double, n: Double) = m + n
    override def minus(m: Double, n: Double) = m - n
    override def times(m: Double, n: Double) = m * n
    override def div(m: Double, n: Double) = m / n
```

Second, define a recursive evaluation of an `Expr`ession given a typeclass instance of `DivisionRing` for `A`:

```Scala
def evalʹ[A](expr: Expr[A])(implicit R: DivisionRing[A], unit: unit): A =
     |   expr match
     |     case Zero      => R.zero
     |     case One       => R.one
     |     case Val(v)    => v
     |     case Inv(n) if unit eq Zero => R.negate(n)
     |     case Inv(n) if unit eq One  => R.reciprocal(n)
     |     case Add(m, n) => R.plus(m, n)
     |     case Mul(m, n) => R.times(m, n)
     |     case Sub(m, n) => R.minus(m, n)
     |     case Div(m, n) => R.div(m, n)
```

Now, because `Id[A]` and `A` are the same type, the implementation is straightforward:

```Scala
val eval: unit ?=> FunctionKʹ[Ring, Expr, Id] =
  new FunctionKʹ[Ring, Expr, Id]:
    def apply[A: Ring](xa: Expr[A]): A =
      evalʹ(xa)(implicitly[Ring[A]].asInstanceOf[DivisionRing[A]])
```

[Previous](https://github.com/sjbiaga/kittens/blob/main/expr-CoflatMap/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/queens-3-trampoline/README.md)
