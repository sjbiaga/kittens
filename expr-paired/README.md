[First](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/expr-simplify/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-tree/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/nat-4-list/README.md)

Lesson 06: Natural Transformations (cont'd)
===========================================

Exercise 06.2
-------------

Using the following `import`, `type`s (rather than `cats.~>`), and `val`ues:

```Scala
import algebra.ring._

type Id[T] = T
type Pair[T] = (T, T)

trait FunctionKʹ[R[_], F[_], G[_]]:
  def apply[A: R](fa: F[A]): G[A]
type FunctionK[F[_], G[_]] = FunctionKʹ[Id, F, G]
type ~>[F[_], G[_]] = FunctionK[F, G]

implicit def id[T]: Id[T] = null.asInstanceOf[Id[T]]

val swap: unit ?=> Expr ~> Expr =
  new (Expr ~> Expr):
    def apply[T: Id](expr: Expr[T]): Expr[T] =
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

implement a natural transformation `val eval: unit ?=> FunctionKʹ[Ring, Expr, Pair]` which evaluates `Expr`essions as well as
their "swaps" downto a `Double`. Note that `R[_]` in `FunctionKʹ[R[_], F[_], G[_]]` is a context bound.

```scala
scala> given unit = One
scala> Inv(Mul(Add(Add(Add(Add(Mul(One, Zero), Val(5.0)), Val(5.0)), Val(5.0)), Val(5.0)), Mul(Mul(Zero, Zero), Zero)))
val res0: Expr[Int | Double] = Inv(Mul(Add(Add(Add(Add(Mul(One,Zero),Val(5.0)),Val(5.0)),Val(5.0)),Val(5.0)),Mul(Mul(Zero,Zero),Zero)))
scala> res0.asInstanceOf[Expr[Double]]
val res1: Expr[Double] = Inv(Mul(Add(Add(Add(Add(Mul(One,Zero),Val(5.0)),Val(5.0)),Val(5.0)),Val(5.0)),Mul(Mul(Zero,Zero),Zero)))
scala> eval(res1)
val res2: Pair[Double] = (Infinity,0.0015923566878980893)
```

Solution
--------

We first have to define a helper method `evalʹ`, which knows how to evaluate an `Expr`ession with base type `A` given an
`implicit` typeclass instance of the `DivisionRing` typeclass for `A`; second, as type `Pair` is a functor, we can define a
natural transformation from `Expr` to `Pair` as the pair of evaluating the expression and its swap using `evalʹ`, and given a
typeclass instance of the `Ring` typeclass for `A` (as instance of `DivisionRing[A]`):

```Scala
def evalʹ[A](expr: Expr[A])(implicit R: DivisionRing[A], unit: unit): A =
  expr match
    case Zero      => R.zero
    case One       => R.one
    case Val(v)    => v
    case Inv(n) if unit eq Zero => R.negate(n)
    case Inv(n) if unit eq One  => R.reciprocal(n)
    case Add(m, n) => R.plus(m, n)
    case Mul(m, n) => R.times(m, n)
    case Sub(m, n) => R.minus(m, n)
    case Div(m, n) => R.div(m, n)

val eval: unit ?=> FunctionKʹ[Ring, Expr, Pair] =
  new FunctionKʹ[Ring, Expr, Pair]:
    def apply[A: Ring](xa: Expr[A]): (A, A) =
      given DivisionRing[A] = implicitly[Ring[A]].asInstanceOf[DivisionRing[A]]
      evalʹ(xa) -> evalʹ(swap(xa)(using if summon[unit] eq Zero then One else Zero))
```

[First](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/expr-simplify/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-tree/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/nat-4-list/README.md)
