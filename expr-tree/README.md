[First](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/expr-paired/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-eert/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/nat-4-list/README.md)

Lesson 06: Natural Transformations (cont'd)
===========================================

Exercise 06.3
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

implement a natural transformation `val eval: unit ?=> FunctionKʹ[Ring, Expr, Tree]` which transforms `Expr`essions into
`Tree`s. Note that `R[_]` in `FunctionKʹ[R[_], F[_], G[_]]` is a context bound.

```scala
scala> Inv(Mul(Add(Add(Add(Add(Mul(One, Zero),Val(5.0)), Val(5.0)), Val(5.0)), Val(5.0)), Mul(Mul(Zero, Zero), Zero)))
val res0: Expr[Int | Double] = Inv(Mul(Add(Add(Add(Add(Mul(One,Zero),Val(5.0)),Val(5.0)),Val(5.0)),Val(5.0)),Mul(Mul(Zero,Zero),Zero)))
scala> res0.asInstanceOf[Expr[Double]]
val res1: Expr[Double] = Inv(Mul(Add(Add(Add(Add(Mul(One,Zero),Val(5.0)),Val(5.0)),Val(5.0)),Val(5.0)),Mul(Mul(Zero,Zero),Zero)))
scala> eval(res1)
val res2: Tree[Double] = Node(Infinity,Inv,None,Some(Node(0.0,Mul,Some(Node(20.0,Add,Some(Node(15.0,Add,Some(Node(10.0,Add,Some(Node(5.0,Add,Some(Node(0.0,Mul,Some(Leaf(1.0)),Some(Leaf(0.0)))),Some(Leaf(5.0)))),Some(Leaf(5.0)))),Some(Leaf(5.0)))),Some(Leaf(5.0)))),Some(Node(0.0,Mul,Some(Node(0.0,Mul,Some(Leaf(0.0)),Some(Leaf(0.0)))),Some(Leaf(0.0)))))))
```

Solution
--------

Because the trees cache the result of their evaluation in the `result` member, we first define a helper method `evalʹ`, which
knows how to evaluate an `Expr`ession with base type `A` given an `implicit` typeclass instance of the `DivisionRing`
typeclass for `A`.

```Scala
implicit def evalʹ[A](expr: Expr[A])(implicit R: DivisionRing[A], unit: unit): A =
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

val eval: unit ?=> FunctionKʹ[Ring, Expr, Tree] =
  new FunctionKʹ[Ring, Expr, Tree]:
    given DivisionRing[A] = implicitly[Ring[A]].asInstanceOf[DivisionRing[A]]
    def apply[A: Ring](xa: Expr[A]): Tree[A] =
      xa match
        case Inv(n)    => Node(evalʹ(xa), Op.Inv, None,           Some(apply(n)))
        case Add(m, n) => Node(evalʹ(xa), Op.Add, Some(apply(m)), Some(apply(n)))
        case Mul(m, n) => Node(evalʹ(xa), Op.Mul, Some(apply(m)), Some(apply(n)))
        case Sub(m, n) => Node(evalʹ(xa), Op.Sub, Some(apply(m)), Some(apply(n)))
        case Div(m, n) => Node(evalʹ(xa), Op.Div, Some(apply(m)), Some(apply(n)))
        case _         => Leaf(evalʹ(xa))
```

This solution is inefficient, because of the evaluation of the subtrees with every node using `evalʹ`. The alternative is
more involved, but simple: we avoid top level `exprʹ`, and use a nested method with the same name that builds the tree while
computing the results in the `DivisionRing[A]` only once.

```Scala
val eval: unit ?=> FunctionKʹ[Ring, Expr, Tree] =
  new FunctionKʹ[Ring, Expr, Tree]:
    def apply[A: Ring](xa: Expr[A]): Tree[A] =
      given DivisionRing[A] = implicitly[Ring[A]].asInstanceOf[DivisionRing[A]]
      def evalʹ(xa: Expr[A]): Tree[A] =
        xa match
          case Inv(n)    =>
            val rhs = evalʹ(n)
            val i = summon[unit] match
              case Zero => given_DivisionRing_A.negate(rhs.result)
              case One  => given_DivisionRing_A.reciprocal(rhs.result)
            Node(i, Op.Inv, None, Some(rhs))
          case Add(m, n) =>
            val (lhs, rhs) = evalʹ(m) -> evalʹ(n)
            val s = given_DivisionRing_A.plus(lhs.result, rhs.result)
            Node(s, Op.Add, Some(lhs), Some(rhs))
          case Sub(m, n) =>
            val (lhs, rhs) = evalʹ(m) -> evalʹ(n)
            val d = given_DivisionRing_A.minus(lhs.result, rhs.result)
            Node(d, Op.Sub, Some(lhs), Some(rhs))
          case Mul(m, n) =>
            val (lhs, rhs) = evalʹ(m) -> evalʹ(n)
            val p = given_DivisionRing_A.times(lhs.result, rhs.result)
            Node(p, Op.Mul, Some(lhs), Some(rhs))
          case Div(m, n) =>
            val (lhs, rhs) = evalʹ(m) -> evalʹ(n)
            val q = given_DivisionRing_A.div(lhs.result, rhs.result)
            Node(q, Op.Div, Some(lhs), Some(rhs))
          case Zero      =>
            Leaf(given_DivisionRing_A.zero)
          case One       =>
            Leaf(given_DivisionRing_A.one)
          case Val(r)    =>
            Leaf(r)
      evalʹ(xa)
```

[First](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/expr-paired/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-eert/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/nat-4-list/README.md)
