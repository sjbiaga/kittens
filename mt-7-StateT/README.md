[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-6-WriterT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

`StateT`
--------

`StateT` is actually a type alias for `IndexedStateT`:

```
type StateT[F[_], S, A] = IndexedStateT[F, S, S, A]
```

while `State` is actually a type alias for `StateT` with `Eval` as effect:

```Scala
type State[S, A] = StateT[Eval, S, A]
```

whereas `IndexedState` is actually a type alias for `IndexedStateT` with `Eval` as effect:

```Scala
type IndexedState[S1, S2, A] = IndexedStateT[Eval, S1, S2, A]
```

Methods à la `map` or `flatMap`
-------------------------------

Methods related to errors
-------------------------

Traversing or folding methods
-----------------------------

`to*` methods
-------------

Other methods
-------------

Methods from the companion object
---------------------------------

Exercise 08.3
=============

Using `State.apply`:

```Scala
def apply[S, A](f: S => (S, A)): State[S, A] =
```

implement an oscillating `State` where the expression keeps constantly swapping and evaluating. Perform this oscillation with
a `for` comprehension and with an infinite `LazyList`.

[Hint: based on the definitions of `swap` and `eval`, use the following type and values:

```Scala
type Stateʹ = State[Expr[Double], Double]
val expr = State { (xa: Expr[Double]) => swap(xa) -> eval(xa) }
lazy val list: LazyList[Stateʹ] = expr #:: list
```

.]

Also, using `IndexedState.apply`:

```Scala
def apply[S1, S2, A](f: S1 => (S2, A)): IndexedState[S1, S2, A]
```

implement a fluctuating `IndexedState`, where `Expr`essions and `Tree`s keep constantly switching one from another. Perform
this fluctuation with a `for` comprehension and with an infinite `LazyList`.

[Hint: based on the natural transformations:

```Scala
def expressify(implicit R: DivisionRing[?]): unit ?=> Tree ~> Expr =
    new (Tree ~> Expr):
      def apply[A](tree: Tree[A]): Expr[A] =
        val (zero, one) = (R.zero, R.one)
        def applyʹ(ta: Tree[A]): TailRec[Expr[A]] =
          ta match
            case Node(_, Op.Inv, _,       Some(n)) =>
              for
                nʹ <- tailcall { applyʹ(n) }
              yield
                Inv(nʹ)
            case Node(_, Op.Add, Some(m), Some(n)) =>
              for
                mʹ <- tailcall { applyʹ(m) }
                nʹ <- tailcall { applyʹ(n) }
              yield
                Add(mʹ, nʹ)
            case Node(_, Op.Sub, Some(m), Some(n)) =>
              for
                mʹ <- tailcall { applyʹ(m) }
                nʹ <- tailcall { applyʹ(n) }
              yield
                Sub(mʹ, nʹ)
            case Node(_, Op.Mul, Some(m), Some(n)) =>
              for
                mʹ <- tailcall { applyʹ(m) }
                nʹ <- tailcall { applyʹ(n) }
              yield
                Mul(mʹ, nʹ)
            case Node(_, Op.Div, Some(m), Some(n)) =>
              for
                mʹ <- tailcall { applyʹ(m) }
                nʹ <- tailcall { applyʹ(n) }
              yield
                Div(mʹ, nʹ)
            case Leaf(`zero`)                      => done(Zero)
            case Leaf(`one`)                       => done(One)
            case Leaf(r)                           => done(Val(r))
        applyʹ(tree).result
```

and:

```Scala
def treeify(implicit R: DivisionRing[?], unit: unit, `0`: `0`[?], `1`: `1`[?]): Expr ~> Tree =
  new (Expr ~> Tree):
    def apply[A](expr: Expr[A]): Tree[A] =
      given DivisionRing[A] = R.asInstanceOf[DivisionRing[A]]
      given `0`[A] = `0`.asInstanceOf[`0`[A]]
      given `1`[A] = `1`.asInstanceOf[`1`[A]]
      def applyʹ(xa: Expr[A]): TailRec[Tree[A]] =
        xa match
          case Add(xm, xn) =>
            for
              m <- tailcall { applyʹ(xm) }
              n <- tailcall { applyʹ(xn) }
            yield
              Node(eval(xa), Op.Add, Some(m), Some(n))
          case Sub(xm, xn) =>
            for
              m <- tailcall { applyʹ(xm) }
              n <- tailcall { applyʹ(xn) }
            yield
              Node(eval(xa), Op.Sub, Some(m), Some(n))
          case Mul(xm, xn) =>
            for
              m <- tailcall { applyʹ(xm) }
              n <- tailcall { applyʹ(xn) }
            yield
              Node(eval(xa), Op.Mul, Some(m), Some(n))
          case Div(xm, xn) =>
            for
              m <- tailcall { applyʹ(xm) }
              n <- tailcall { applyʹ(xn) }
            yield
              Node(eval(xa), Op.Div, Some(m), Some(n))
          case Inv(xn)     =>
            for
              n <- tailcall { applyʹ(xn) }
            yield
              Node(eval(xa), Op.Inv, None, Some(n))
          case _           => done(Leaf(eval(xa)))
      applyʹ(expr).result
```

use the following type and values:

```Scala
type Stateʹ[F[_], G[_]] = IndexedState[F[Double], G[Double], Double]

var expr = IndexedState { (xa: Expr[Double]) => treeify.apply(xa) -> eval(xa) }
var tree = IndexedState { (ta: Tree[Double]) => expressify.apply(ta) -> ta.result }

lazy val list: LazyList[Stateʹ[Expr, Tree]] = expr #:: list
lazy val listʹ: LazyList[Stateʹ[Tree, Expr]] = tree #:: listʹ
```

.]

What difference is manifest when alternating by oscillation versus fluctuation?

Solution - Part 1
-----------------

The `swap` method is the same as before - as well the builder and the parser. In order to abstract away from `Double`, we use
the `Zero[_]` and `One[_]` typeclasses from `alleycats`:

```Scala
import algebra.ring.{ DivisionRing, Ring }
import alleycats.{ Zero => `0`, One => `1` }

implicit val kittensDoubleRing: DivisionRing[Double] =
  new DivisionRing[Double]:
    override val zero = 0d
    override val one = 1d
    override def negate(n: Double) = 0d - n
    override def reciprocal(n: Double) = 1d / n
    override def plus(m: Double, n: Double) = m + n
    override def minus(m: Double, n: Double) = m - n
    override def times(m: Double, n: Double) = m * n
    override def div(m: Double, n: Double) = m / n

def eval[A](expr: Expr[A])(implicit R: DivisionRing[A], unit: unit, `0`: `0`[A], `1`: `1`[A]): A =
  def evalʹ(xa: Expr[A]): TailRec[A] =
    xa match
      case Zero => done(`0`.zero)
      case One => done(`1`.one)
      case Val(n) => done(n)
      case Inv(xn) if Zero eq unit =>
        for
          n <- tailcall { evalʹ(xn) }
        yield
          R.minus(`0`.zero, n)
      case Inv(xn) if One eq unit =>
        for
          n <- tailcall { evalʹ(xn) }
        yield
          R.div(`1`.one, n)
      case Add(xm, xn)       =>
        for
          m <- tailcall { evalʹ(xm) }
          n <- tailcall { evalʹ(xn) }
        yield
          R.plus(m, n)
      case Sub(xm, xn)       =>
        for
          m <- tailcall { evalʹ(xm) }
          n <- tailcall { evalʹ(xn) }
        yield
          R.times(m, n)
      case Mul(xm, xn)       =>
        for
          m <- tailcall { evalʹ(xm) }
          n <- tailcall { evalʹ(xn) }
        yield
          R.times(m, n)
      case Div(xm, xn)       =>
        for
          m <- tailcall { evalʹ(xm) }
          n <- tailcall { evalʹ(xn) }
        yield
          R.div(m, n)
  evalʹ(expr).result
```

We can use either `for` comprehension or an infinte `LazyList` to oscillate:

```Scala
given unit = Zero

given `0`[Double] = `0`(0d)
given `1`[Double] = `1`(1d)

var x =
  Builder.start(x"0")
  .add(One)
  .multiply(Val(5d), 4)
    .open(One)
    .add(One, 2)
    .close(_.add(_))
  .lhs
  .asInstanceOf[Expr[Double]]

val expr = State { (xa: Expr[Double]) => swap(xa) -> eval(xa) }

println {
  ( for
      _ <- expr
      x <- expr
    yield
      x
  ).run(x).value
}

lazy val list: LazyList[Stateʹ] = expr #:: list

println { list.take(3).foldRight(x)(_.run(_).value._1) }
```

We used `foldRight` in order to pass an anonymous function - for brevity. We invoke `IndexedStateT#run` method w

Solution - Part 2
-----------------

```Scala
given unit = Zero

given `0`[Double] = `0`(0d)
given `1`[Double] = `1`(1d)

var x =
  Builder.start(x"0")
  .add(One)
  .multiply(Val(5d), 4)
    .open(One)
    .add(One, 2)
    .close(_.add(_))
  .lhs
  .asInstanceOf[Expr[Double]]

val t = treeify.apply(x)

var expr = IndexedState { (xa: Expr[Double]) => treeify.apply(xa) -> eval(xa) }
var tree = IndexedState { (ta: Tree[Double]) => expressify.apply(ta) -> ta.result }

println {
  ( for
      _ <- expr
      _ <- tree
      x <- expr
    yield
      x
  ).run(x).value
}

println {
  ( for
      _ <- tree
      _ <- expr
      t <- tree
    yield
      t
  ).run(t).value
}

lazy val list: LazyList[Stateʹ[Expr, Tree]] = expr #:: list
lazy val listʹ: LazyList[Stateʹ[Tree, Expr]] = tree #:: listʹ

println {
  (list zip listʹ).take(3).foldLeft(Left(x): Expr[Double] Either Tree[Double]) {
    case (Left(expr), (self, _))  => Right(self.run(expr).value._1)
    case (Right(tree), (_, self)) => Left(self.run(tree).value._1)
  }.right.get
}
```

Solution - Part 3
-----------------

The difference is that when _fluctuating_, `expr` and `tree` must alternate, depending on which are the first state and last
state .

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-6-WriterT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)
