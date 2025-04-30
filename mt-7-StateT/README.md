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

A `State` _describes_ a computation, it is not itself the "state of the computation": a computation can be

- a line by line invocation of some `run` method (for the `Eval` effect, intermediated by `Eval#value` invocations);

- a fold or reduce operation, such as `foldLeft`.

---

Let us propound to compute the average of any sequence of `Double`s: the ratio between their sum (a `Double`) and their count
(an `Int`eger). We model the state to be the tuple `(Int, Double)`, and as value - a `Double`. We design with two functions:
`avg` used to maintain the `State`, and `add` used to prepend an (average) computation node to a `LazyList`:

```scala
scala> type Stateʹ = State[(Int, Double), Double]

scala> def avg(d: Double): Stateʹ =
     |   State {
     |     case (count: Int, sum: Double) =>
     |       ((count + 1, sum + d), (sum + d) / (count + 1))
     |   }
     |

scala> def add(d: Double, t: LazyList[Stateʹ] = LazyList.empty): LazyList[Stateʹ] = avg(d) #:: t
```

Let us add the first four powers of ten:

```scala
scala> add(1, add(10, add(100, add(1000))))
val res0: LazyList[Stateʹ] = LazyList(<not computed>)
```

In order to compute their average, all that is required is to `foldLeft` starting from the zero counter and sum, and with a
`Double.NaN` as a dummy "average", and thread the states through the
`IndexedStateT#run: (Int, Double) => Eval[((Int, Double), Double)]` method - as function (second) parameter to `foldLeft`:

```scala
scala> res0.foldLeft(0 -> 0.0 -> Double.NaN) { case ((state, _), node) => node.run(state).value }
val res1: ((Int, Double), Double) = ((4,1111.0),277.75)
```

The average is in the second element of the pair.

Now if we want to continue adding the same `LazyList`, all we have to do is pass `res1` as initial accumulator to `foldLeft`:

```scala
scala> res0.foldLeft(res1) { case ((state, _), node) => node.run(state).value }
val res2: ((Int, Double), Double) = ((8,2222.0),277.75)
```

Because the new sum is the double of the previous, and the count is twice too, the number two in the fraction cancels out, so
the average is the same. If we continue to average the first four multiples of five, the new average (continued with `res2`)
will be `190.1(6)`:

```scala
scala> add(5, add(10, add(20, add(25))))
val res3: LazyList[Stateʹ] = LazyList(<not computed>)

scala> res3.foldLeft(res2) { case ((state, _), node) => node.run(state).value }
val res4: ((Int, Double), Double) = ((12,2282.0),190.16666666666666)
```

Is there another way we could implement the average of a _random_ sequence of `Double`s?! We would like to use the following
infinite list:

```scala
scala> import scala.util.Random.nextDouble

scala> def inf: LazyList[Double] = nextDouble #:: inf
def inf: LazyList[Double]
```

We can thus combine the use of a `LazyList` inside the average computation itself (from a parameter, `d` becomes a variable
pattern - note that `avg` is merely a value, there is _no_ `LazyList` _parameter_, only pattern matching on one):

```scala
scala> type Stateʹʹ = State[(Int, Double, LazyList[Double]), Double]
scala> val avg: Stateʹʹ =
     |   State {
     |     case (count, sum, d #:: t) =>
     |       ((count + 1, sum + d, t), (sum + d) / (count + 1))
     |     case (count, sum, nil) =>
     |       ((count, sum, nil), sum / count)
     |   }
     |
val avg: Stateʹʹ = cats.data.IndexedStateT@4d204b30
```

Now, there is just one value, all that is needed is to pass it the initial state, which contains an _infinite_ list. Note
that `count` is now limited by how many times we invoke `IndexedStateT#run` on the `avg` value (had we used a finite `List`,
the limit would have been its size):

```scala
scala> inf.take(10).foldLeft(avg.run((0, 0.0, inf))) { case (state, _) => avg.run(state.value._1) }
val res5: cats.Eval[((Int, Double, LazyList[Double]), Double)] = cats.Eval$$anon$4@6b26fe0a

scala> res5.value
val res6: ((Int, Double, LazyList[Double]), Double) = ((11,4.591147974500079,LazyList(<not computed>)),0.41737708859091627)
```

We can similarly continue the computation from `res6` (there is no need to specify the `LazyList` anymore):

```scala
scala> inf.take(10).foldLeft(avg.run(res6._1)) { case (state, _) => avg.run(state.value._1) }
val res7: cats.Eval[((Int, Double, LazyList[Double]), Double)] = cats.Eval$$anon$4@423ea10e

scala> res7.value
val res8: ((Int, Double, LazyList[Double]), Double) = ((22,10.78058960388977,LazyList(<not computed>)),0.4900268001768077)
```

Exercise 08.3
=============

Turn `avg` into a method with an `Int` parameter - the reset counter, thus computing the average only for each _window_, and
not for the whole sequence. Add a callback parameter which is invoked for each window once. What happens when the length of
the list is a multiple of the size of the window?

Do the same for one more computation with `State`: either `min` or `max`.

Solution - Part 1
-----------------

Whenever the counter equals the `size` of the window, the callback is invoked, and the computation will continue with the
counter equal to one, the sum and average equal to the current element:

```scala
scala> def avgʹ(size: Int, cb: Double => Unit): Stateʹʹ =
     |   State {
     |     case (0, _, d #:: t) =>
     |       ((1, d, t), d)
     |     case (`size`, sum, d #:: t) =>
     |       cb(sum / size)
     |       ((1, d, t), d)
     |     case (count, sum, d #:: t) =>
     |       ((count + 1, sum + d, t), (sum + d) / (count + 1))
     |     case (`size`, sum, nil) =>
     |       cb(sum / size)
     |       ((0, Double.NaN, nil), Double.NaN)
     |     case (count, sum, nil) =>
     |       ((count, sum, nil), sum / count)
     |   }
```

Let `avg` be the computation of average for windows of size four; then we have:

```scala
scala> val avg = avgʹ(4, println)
val avg: Stateʹʹ = cats.data.IndexedStateT@1431f9b5

scala> inf.take(10).foldLeft(avg.run((0, Double.NaN, inf))) { case (state, _) => avg.run(state.value._1) }
0.6491109214966045
0.4667552365636114
val res9: cats.Eval[((Int, Double, LazyList[Double]), Double)] = cats.Eval$$anon$4@53d1cd85

scala> res9.value
val res10: ((Int, Double, LazyList[Double]), Double) = ((3,2.2530923940316683,LazyList(<not computed>)),0.751030798010556)

scala> inf.take(10).foldLeft(avg.run(res10._1)) { case (state, _) => avg.run(state.value._1) }
0.7298302325394203
0.5411544219642497
0.34223248012134266
val res11: cats.Eval[((Int, Double, LazyList[Double]), Double)] = cats.Eval$$anon$4@32dbc27f

scala> res11.value
val res12: ((Int, Double, LazyList[Double]), Double) = ((2,0.7412616724619366,LazyList(<not computed>)),0.3706308362309683)
```

When the length of the list is a multiple of the size of the window, the callback must be invoked, but the computation should
stop with a zero counter, `Double.NaN` sum and average, and the empty list.

```scala
scala> inf.take(4).foldLeft(avg.run((0, Double.NaN, inf.take(4)))) { case (state, _) => avg.run(state.value._1) }
val res13: cats.Eval[((Int, Double, LazyList[Double]), Double)] = cats.Eval$$anon$4@5079123

scala> res13.value
0.5662005202414435
val res14: ((Int, Double, LazyList[Double]), Double) = ((0,NaN,LazyList()),NaN)
```

Solution - Part 2
-----------------

To compute `min` or `max` is much simpler, but still an aggregation which uses a counter to detect the windows:

```scala
scala> def minʹ(size: Int, cb: Double => Unit): Stateʹʹ =
     |   State {
     |     case (0, _, d #:: t) =>
     |       ((1, d, t), d)
     |     case (`size`, min, d #:: t) =>
     |       cb(min)
     |       ((1, d, t), d)
     |     case (count, min, d #:: t) =>
     |       ((count + 1, min min d, t), min min d)
     |     case (`size`, min, nil) =>
     |       cb(min)
     |       ((0, Double.NaN, nil), 0.0)
     |     case (count, min, nil) =>
     |       ((count, min, nil), min)
     |   }
```

---

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

Exercise 08.4
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

implement a fluctuating `IndexedState`, where `Expr`essions and `Tree`s keep constantly switching from one another. Perform
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
