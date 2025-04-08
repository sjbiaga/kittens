[Previous](https://github.com/sjbiaga/kittens/blob/main/expr-tree/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/eval-1-function0/README.md)

Lesson 06: Natural Transformations (cont'd)
===========================================

Exercise 06.4
-------------

Using the following `import`, `type`s (rather than `cats.~>`), and `val`ues:

```Scala
import algebra.ring._

enum Op:
  case Add, Sub, Mul, Div, Inv
enum Tree[T]:
  val result: T
  case Leaf[T](override val result: T) extends Tree[T]
  case Node[T](override val result: T,
               operator: Op,
               left: Option[Tree[T]],
               right: Option[Tree[T]]) extends Tree[T]

import Tree._

trait FunctionKʹ[R[_], F[_], G[_]]:
  def apply[A: R](fa: F[A]): G[A]

implicit def id[T]: Id[T] = null.asInstanceOf[Id[T]]

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

implement a natural transformation `val lave: unit ?=> FunctionKʹ[Ring, Tree, Expr]` which transforms `Tree`s into
`Expr`essions. Note that `R[_]` in `FunctionKʹ[R[_], F[_], G[_]]` is a context bound.

Solution
--------

This is the opposite of `eval` from the previous Exercise 06.3, so we call it `lave` (read "eval" from right to left):

```Scala
 val lave: unit ?=> FunctionKʹ[Ring, Tree, Expr] =
    new FunctionKʹ[Ring, Tree, Expr]:
      def apply[A: Ring](ta: Tree[A]): Expr[A] =
        given DivisionRing[A] = implicitly[Ring[A]].asInstanceOf[DivisionRing[A]]
        ta match
          case Node(_, Op.Inv, _,       Some(n)) => Inv(apply(n))
          case Node(_, Op.Add, Some(m), Some(n)) => Add(apply(m), apply(n))
          case Node(_, Op.Sub, Some(m), Some(n)) => Sub(apply(m), apply(n))
          case Node(_, Op.Mul, Some(m), Some(n)) => Mul(apply(m), apply(n))
          case Node(_, Op.Div, Some(m), Some(n)) => Div(apply(m), apply(n))
          case Leaf(r)
            if r == given_DivisionRing_A.zero    => Zero
          case Leaf(r)
            if r == given_DivisionRing_A.one     => One
          case Leaf(r)                           => Val(r)
```

[Previous](https://github.com/sjbiaga/kittens/blob/main/expr-tree/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/eval-1-function0/README.md)
