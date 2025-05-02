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

The state is kept "between the lines", respectively, probably in a "`while`" loop.

An `IndexedStateT` is a `class` with an effect parameter `F[_]`, two types for the states, `SA` and `SB`, and one type for
the output, `A`: it composes `F` with the function `SA => F[(SB, A)]`.

```Scala
final class IndexedStateT[F[_], SA, SB, A](val runF: F[SA => F[(SB, A)]])
```

`run*` methods
--------------

There are a total of six `run*` methods - not counting the parameter `runF` -, each of return type `F[T]` for some `T`, and
all resorting to the main one `run`:

```Scala
def run(initial: SA)(implicit F: FlatMap[F]): F[(SB, A)] =
  F.flatMap(runF)(_(initial))
```

So, if `F` is a `FlatMap`, a _step_ of computation can be performed with `run`: but the result has the pair of the next state
and the output, still lifted in `F`.

There are two groups of three methods each, corresponding to `run` and `runEmpty`; the latter uses a `S: Monoid[SA]` typeclass
instance in order to invoke `run` with `S.empty`:

```Scala
def runEmpty(implicit S: Monoid[SA], F: FlatMap[F]): F[(SB, A)] = run(S.empty)
```

There are two more methods `runS` and `runA`, which result only in the state, respectively, the output:

```Scala
def runS(s: SA)(implicit F: FlatMap[F]): F[SB] = F.map(run(s))(_._1)
def runA(s: SA)(implicit F: FlatMap[F]): F[A] = F.map(run(s))(_._2)
```

as well as two more mirrored methods `runEmptyS` and `runEmptyA`, which result only in the state, respectively, the output,
and resort to `runS` and `runA`:

```Scala
def runEmptyS(implicit S: Monoid[SA], F: FlatMap[F]): F[SB] = runS(S.empty)
def runEmptyA(implicit S: Monoid[SA], F: FlatMap[F]): F[A] = runA(S.empty)
```

The `runEmptyX` method thus resorts to the `runX` method.

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
```

We can thus combine the use of a `LazyList` inside the average computation itself (from a parameter, `d` becomes a variable
pattern - note that `avg` is merely a value, there is _no_ `LazyList` _parameter_, only pattern matching on one):

```scala
scala> type Stateʹ = State[(Int, Double, LazyList[Double]), Double]
scala> val avg: Stateʹ =
     |   State {
     |     case (count, sum, d #:: t) =>
     |       ((count + 1, sum + d, t), (sum + d) / (count + 1))
     |     case (count, sum, nil) =>
     |       ((count, sum, nil), sum / count)
     |   }
     |
```

Now, there is just one value, all that is needed is to pass it the initial state, which contains an _infinite_ list. Note
that `count` is now limited by _how many times_ we invoke `IndexedStateT#run` on the `avg` value (had we used a finite `List`,
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
scala> def avgʹ(size: Int, cb: Double => Unit): Stateʹ =
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
scala> def minʹ(size: Int, cb: Double => Unit): Stateʹ =
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

In order to understand how the following methods work, is worth to keep in mind that `runF` lifted a _function_ into the `F`
effect, so the "creation" of another `IndexedStateT` object will always appeal to composition of functions, while the
invocation of method `run` on such a receiver, will always apply the "initial" state to the resulting function. Also, the
function "from" `runF` yields a lifted pair `F[(SB, A)]`, so we would expect the involvement of `F.map` and `F.flatMap` a lot
to perform the wrapping/unwrapping.

Methods à la `map` or `flatMap`
-------------------------------

Five methods `map`, `modify`, `bimap`, `inspect`, and `get`, resort to the `transform` method:

```Scala
def transform[SC, B](f: (SB, A) => (SC, B))(implicit F: Functor[F]): IndexedStateT[F, SA, SC, B] =
  IndexedStateT.applyF(F.map(runF) { AndThen(_) andThen F.lift(f.tupled) })
```

which delegates to the [companion object](#methods-from-the-companion-object)'s method `applyF`. Let us make type ascriptions
and re-define `transform` thus:

```Scala
def transform[SC, B](f: (SB, A) => (SC, B))(implicit F: Functor[F]): IndexedStateT[F, SA, SC, B] =
  IndexedStateT.applyF {
    F.map(runF) { (safsba: SA => F[(SB, A)]) =>
      AndThen(safsba) andThen { (fsba: F[(SB, A)]) =>
        F.lift(f.tupled)(fsba): F[(SC, B)]
      }: SA => F[(SC, B)]
    }: F[SA => F[(SC, B)]]
  }
```

From the first (`safsba: SA => F[(SB, A)]`) and last ascriptions (`F[SA => F[(SC, B)]]`), we can deduce that the _functional_
expression which is computed in the (outer) block with parameter `safsba` has type `(SA => F[(SB, A)]) => (SA => F[(SC, B)])`,
which is a higher-order function type. Thus, the value passed to `IndexedStateT.applyF` is the result of the computation of
another expression:

```Scala
F.map(runF: F[SA => F[(SB, A)]]) { <functional expression>: (SA => F[(SB, A)]) => (SA => F[(SC, B)]) }: F[SA => F[(SC, B)]]
//            ----------------                               ----------------      ++++++++++++++++       ++++++++++++++++
```

which type checks as ascribed.

In the inner block with parameter `fsba: F[(SB, A)]`, we can make the following two ascriptions for the partial application:

```Scala
F.lift(f.tupled: ((SB, A)) => (SC, B)): F[(SB, A)] => F[(SC, B)]
```

All that is left now is to apply the second parameter `fsba` - that type checks. Of course, we could have written as well:

```Scala
F.map(fsba: F[(SB, A)])(f.tupled): F[(SC, B)]
```

### Methods based on `transform`

1. The method `bimap` is at the base of two symmetric methods: `map` and `modify`. The function parameter to `transform`, of
   type `(SB, A) => (SC, B)`, is passed as an anonymous function:

```Scala
def bimap[SC, B](f: SB => SC, g: A => B)(implicit F: Functor[F]): IndexedStateT[F, SA, SC, B] =
  transform(f(_) -> g(_))
```

which creates a pair of type `(SC, B)` from two arguments of type `(SA, A)` by applying the first function parameter `f` to
the first argument of type `SA`, and the second function parameter `g` to the second argument of type `A`. The anonymous
function `f(_) -> g(_)` is a _binary_ function - not a unary function with type a tuple -, but its result is a _pair_.

`bimap` is also quasi-aliased by the `map` and `modify` methods:

```Scala
def map[B](f: A => B)(implicit F: Functor[F]): IndexedStateT[F, SA, SB, B] =
  bimap(identity: SA => SA, f)
def modify[SC](f: SB => SC)(implicit F: Functor[F]): IndexedStateT[F, SA, SC, A] =
  bimap(f, identity: A => A)
```

Both `map` and  `modify` invoke `bimap` with the same names of parameters, but in a different order (and of different types
in the choice of the type parameters). The former is also one of the two methods required to turn `IndexedStateT` into a monad.

It is interesting how two totally unrelated methods - such as `map` and `modify` - can resort to practically the same
implementation. The latter is used to change the state, while the former is used to change the (output) type of `IndexedStateT`.

2. The method `map` can also be defined as a quasi-alias to `transform`, passing it a binary anonymous function:

```Scala
def map[B](f: A => B)(implicit F: Functor[F]): IndexedStateT[F, SA, SB, B] =
  transform(_ -> f(_))
```

A _placeholder_ that is _bare_ (not involved in any expression) stands for the `identity` function, but in fact is just a
parameter that occurs _once_ and without being _involved_ in any expression. Thus, the new "final" state is kept identical.

3. The method `modify` can be defined symmetrically as a quasi-alias to `transform`, passing it a binary anonymous function:

```Scala
def modify[SC](f: SB => SC)(implicit F: Functor[F]): IndexedStateT[F, SA, SC, A] =
  transform(f(_) -> _)
```

Notice again that the second placeholder is bare, so the output is kept identical.

4. The method `inspect` is a quasi-alias to `transform`, passing it a binary function that alters the (output) type of the
   `IndexedStateT`, while keeping the same state:

```Scala
def inspect[B](f: SB => B)(implicit F: Functor[F]): IndexedStateT[F, SA, SB, B] =
  transform((s, _) => (s, f(s)))
```

Because the state is preserved, invoking `inspect` several times with identical function parameter, maintains a "constant"
`IndexedStateT` object (although _instantiated_ multiple times).

5. Not to apply a function for the output, `get` is an alias for `inspect` with `identity` as function argument:

```Scala
def get(implicit F: Functor[F]): IndexedStateT[F, SA, SB, SB] =
  inspect(identity)
```

---

In order to be possible to be implemented, `flatMap` requires that the _first_ state type parameter in the result of type
`IndexedStateT[F[_], SB, SC, B]` of the function parameter - which is `SB` -, be identical with the _second_ state type
parameter in the type of the receiver `IndexedStateT[F[_], SA, SB, B]` - which is `SB`:

```Scala
def flatMap[SC, B](fas: A => IndexedStateT[F, SB, SC, B])(implicit F: FlatMap[F]): IndexedStateT[F, SA, SC, B] =
  IndexedStateT.applyF(F.map(runF) { safsba =>
    AndThen(safsba).andThen { fsba =>
      F.flatMap(fsba) { case (sb, a) =>
        fas(a).run(sb)
      }
    }
  })
```

With this occasion, we can also observe how the type parameters used in the translation of `for`-comprehension are detected:

1. the argument type of the function parameter to `flatMap` is identified as `A`

1. for `IndexedStateT`, this occurs the fourth in the list of type parameters: `F[_]`, `SA`, `SB`, and `A`

1. the fourth position is thus reserved for the change of type during `flatMap`, which in this case is named `B`

1. `B` could be a "constant" type (like `Unit`), or a type parameter to `flatMap` - in this case, the second

1. when the expression that is passed as function argument to `flatMap` is type checked, so do the other type parameters in
   the signature of `flatMap` must type check - in this case, the result of the said expression must be of type
   `IndexedStateT`, of the same effect `F`, and with the second type parameter being `SB`

1. the source type of the resulting `IndexedStateT[F, SA, SC, B]` remains the same `SA`

1. the "adaptable" type parameters `SC` and `B` are there for flexibility when the `IndexedStateT` receiver is a generator in
   a `for` comprehension.

When the result will be invoked method `run` upon, the implementation of `flatMap` knows how to apply functions and calculate
expressions, such that an argument `a: A` is applied to `fas`, and method `run` is invoked upon the resulting receiver
`IndexedStateT[F, SB, SC, B]` with an "initial" state `sb: SB`, as well. With this last observation, let us ascribe types to
the function parameters and return types:

```Scala
def flatMap[SC, B](fas: A => IndexedStateT[F, SB, SC, B])(implicit F: FlatMap[F]): IndexedStateT[F, SA, SC, B] =
  IndexedStateT.applyF {
    F.map(runF) { (safsba: SA => F[(SB, A)]) =>
      AndThen(safsba).andThen { (fsba: F[(SB, A)]) =>
        F.flatMap(fsba) { case (sb: SB, a: A) =>
          fas(a).run(sb): F[(SC, B)]
        }: F[(SC, B)]
      }: SA => F[(SC, B)]
    }: F[SA => F[(SC, B)]]
  }
```

So, `F.map(runF)` passes an argument function of type `SA => F[(SB, A)]` to the block with parameter `safsba`. Because this
_value_ is a function (but still a value), we can have the block return a _functional_ expression: a "composition" - via
`andThen` - of the object `AndThen(safsba)` with the block with parameter `fsba`, a result of type `SA => F[(SC, B)]`; which
makes `F.map(runF) { safsba => ... }` lift it to type `F[SA => F[(SC, B)]]`.

As for the block with parameter `fsba`, it passes this to `F.flatMap(fsba)`, which passes a pair `(SB, A)` to `flatMap`'s
innermost block in turn. The return expression is `fas(a: A).run(sb: SB)` - having had computed both the argument `a` and the
"initial" state `sb` -, resulting in a pair `(SC, B)` ("final" state, output), that already got lifted into `F` effect as
`F[(SC, B)]`, and that `F.flatMap(fsba) { ... }` knows to preserve.

Note that `flatMap` can also be defined shorter using an anonymous function and `F.liftFM`:

```Scala
def flatMap[SC, B](fas: A => IndexedStateT[F, SB, SC, B])(implicit F: FlatMap[F]): IndexedStateT[F, SA, SC, B] =
  IndexedStateT.applyF(F.map(runF) {
    AndThen(_) andThen F.liftFM { case (sb, a) => fas(a).run(sb) }
  })
```

where `liftFM` is defined in the `FlatMap[F[_]]` trait:

```Scala
def liftFM[A, B](f: A => F[B]): F[A] => F[B] = flatMap(_)(f)
```

A variant of `flatMap` for the case where the function parameter is reduced in the return type to a `B` lifted in the effect
`F`, is method `flatMapF`:

```Scala
def flatMapF[B](faf: A => F[B])(implicit F: FlatMap[F]): IndexedStateT[F, SA, SB, B] =
  IndexedStateT.applyF(F.map(runF) {
    AndThen(_) andThen F.liftFM { case (sb, a) => F.map(faf(a))((sb, _)) }
  })
```

The "final" state is not modified when the method `run` is invoked on the resulting `IndexedStateT[F, SA, SB, B]`, invocation
which first applies the "initial" state of type `SA` to the unwrapped `SA => F[(SB, A)]` function; function which - wrapped
in an `AndThen` object - is "composed" with another of type `F[(SB, A)] => F[(SB, B)]` - by making the following ascriptions:

```Scala
F.map(faf(a): F[B])((sb, _)): F[(SB, B)]
F.liftFM { case (sb: SB, a: A) => F.map(faf(a))((sb, _)) }: F[(SB, A)] => F[(SB, B)]
```

So, when composing with `andThen`, the "middle" type `F[(SB, A)]` - that allows the "composition" - vanishes.

Other methods
-------------

`mapK`, `transformS`

The partial function application `F.map(runF)` allows for the second parameter to _involve_ the type `SA => F[(SB, A)]`. But
this is a _function_ type. In the methods `transform`, `flatMap`, and `flatMapF`, we have seen how it was used to "compose to
the left" with a function of _source_ type `F[(SB, A)]`. The "composition to the right" is also possible, with a function
of _target_ type `SA`, e.g., `F.map(runF)(f andThen _)`, where `f: ? => SA`. This is how `contramap` is definable:

```Scala
def contramap[S0](f: S0 => SA)(implicit F: Functor[F]): IndexedStateT[F, S0, SB, A] =
  IndexedStateT.applyF(F.map(runF)(f andThen _))
```

Exercise 08.4
=============

Using similar types, methods and `State`-values from [Exercise 08.3](#exercise-083):

```scala
scala> type Stateʹ[A] = State[(Int, A, LazyList[A]), A]
scala> def avgʹ(size: Int, cb: Double => Unit): Stateʹ[Double] = ???
scala> val avg = avgʹ(4, println)
```

compute the averages _of_ `Int`egers - using `contramap` -, _as_ rounded `Double`s.

Solution
--------

The data from [Exercise 08.3](#exercise-083) are:

```scala
scala> type Stateʹ[A] = State[(Int, A, LazyList[A]), A]

scala> def avgʹ(size: Int, cb: Double => Unit): Stateʹ[Double] =
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

scala> val avg = avgʹ(3, println)
```

We change the type of the "initial" state - to be based on `Int` - using `contramap`:

```scala
scala> avg.contramap[(Int, Int, LazyList[Int])] { case (count, sum, list) => (count, sum.toDouble, list.map(_.toDouble)) }
val res0:
  cats.data.IndexedStateT[cats.Eval, (Int, Int, LazyList[Int]),
    (Int, Double, LazyList[Double]), Double] = cats.data.IndexedStateT@2f7edfcf
```

The infinite list has `Int` base type. Because the "final" state is based on `Double`, we have to convert back to a state
based on `Int` - the type of the accumulator-state:

```scala
scala> def inf(n: Int = 1): LazyList[Int] = n #:: inf(n + 1)

scala> inf().take(10).foldLeft(res0.run((0, Int.MinValue, inf()))) {
     |   case (state, _) =>
     |     val ((count, sum, list), _) = state.value
     |     res0.run((count, sum.toInt, list.map(_.toInt)))
     | }
2.0
5.0
8.0
val res1: cats.Eval[((Int, Double, LazyList[Double]), Double)] = cats.Eval$$anon$1@5f188628
```

---

The `dimap` method resorts to - as a particular case of using - two other methods, namely `contramap` and `modify`:

```Scala
def dimap[S0, S1](f: S0 => SA)(g: SB => S1)(implicit F: Functor[F]): IndexedStateT[F, S0, S1, A] =
  contramap(f).modify(g)
```

`dimap` is "contravariant" in its first function parameter `f`, and "covariant" in its second function parameter `g`, which
is why it is able to (invoke) `contramap` with `f` as argument, and _then_ (invoke) `modify` with `g` as argument.

Exercise 08.5
=============

Implement the `imap` extension method to `IndexedStateT[F, SA, SB, A]`, that uses a typeclass instance of the `Invariant`
typeclass for the effect `F`, to invoke the homonym method on a receiver `I: Invariant[F]`:

```Scala
extension [F[_], SA, SB, A](self: IndexedStateT[F, SA, SB, A])
  def imap[SC](f: SB => SC)(g: SC => SB)(implicit F: Functor[F], I: Invariant[F]): IndexedStateT[F, SA, SC, A] =
```

[Hint: fill in the blanks in the following code:

```Scala
scala> import cats._, cats.data._

def imap[SC](f: SB => SC)(g: SC => SB)(implicit F: Functor[F], I: Invariant[F]): IndexedStateT[F, SA, SC, A] =
  IndexedStateT.applyF {
    F.map(runF) {
      AndThen(_: SA => F[(SB, A)]).andThen {
        I.imap(_: F[(SB, A)]) { ... } { ... }
      }: SA => F[(SC, A)]
    }: F[SA => F[(SC, A)]]
  }
```

where the `imap` method is defined thus:

```Scala
trait Invariant[F[_]] ... {
  def imap[X, Y](fa: F[X])(f: X => Y)(g: Y => X): F[Y]
}
```

Substitute `(SB, A)` for `X` and `(SC, A)` for `Y`.]

Using similar methods and `State`-values from [Exercise 08.3](#exercise-083), as well as methods and values about a new case
class `Avg`:

```scala
scala> def avgʹ(size: Int, cb: Double => Unit): State[(Int, Double, LazyList[Double]), Double] =
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
     |

scala> case class Avg(count: Int, sum: Double, list: LazyList[Double])
scala> def avgʹʹ(size: Int, cb: Double => Unit): State[Avg, Double] =
     |   State {
     |     case Avg(0, _, d #:: t) =>
     |       (Avg(1, d, t), d)
     |     case Avg(`size`, sum, d #:: t) =>
     |       cb(sum / size)
     |       (Avg(1, d, t), d)
     |     case Avg(count, sum, d #:: t) =>
     |       (Avg(count + 1, sum + d, t), (sum + d) / (count + 1))
     |     case Avg(`size`, sum, nil) =>
     |       cb(sum / size)
     |       (Avg(0, Double.NaN, nil), Double.NaN)
     |     case Avg(count, sum, nil) =>
     |       (Avg(count, sum, nil), sum / count)
     |   }
     |
scala> def inf(n: Double = 1.0): LazyList[Double] = n #:: inf(n + 1)
scala> val avg = avgʹ(3, println)
scala> val AVG = avgʹʹ(3, println)
```

find a use case for the `imap` extension method just implemented.

Solution - Part 1
-----------------

The anonymous innermost function:

```Scala
extension [F[_], SA, SB, A](self: IndexedStateT[F, SA, SB, A])
  def imap[SC](f: SB => SC)(g: SC => SB)(implicit F: Functor[F], I: Invariant[F]): IndexedStateT[F, SA, SC, A] =
    IndexedStateT.applyF {
      F.map(runF) {
        AndThen(_) andThen {
          I.imap(_) { case (sb, a) => (f(sb), a) } { case (sc, a) => (g(sc), a) }
        }
      }
    }
```

is passed two function arguments, respectively:

```Scala
{ case (sb, a) => (f(sb), a) }
{ case (sc, a) => (g(sc), a) }
```

where `(sb, a): (SB, A)` and `(sc, a): (SC, A)`, and so `a` is kept as output, whereas, respectively, `f` is applied `sb` and
`g` is applied `sc`.

Solution - Part 2
-----------------

We invoke `imap` on `avg` and `AVG` values:

```scala
scala> avg.imap(Avg.apply) { it => (it.count, it.sum, it.list) }
val res0:
  cats.data.IndexedStateT[cats.Eval, (Int, Double, LazyList[Double]), Avg,
    Double] = cats.data.IndexedStateT@43ce5381

scala> AVG.imap { it => (it.count, it.sum, it.list) } (Avg.apply)
val res1:
  cats.data.IndexedStateT[cats.Eval, Avg, (Int, Double, LazyList[Double]),
    Double] = cats.data.IndexedStateT@1ab993b2
```

and observe that `res1`'s "initial" state type is `Avg`, same as `res0`'s "final" state type (or, the other way around).
Hence, we [can](#solution---part-3) place them in a `for` comprehension, and then invoke `run` on `res2`:

```scala
scala> for
     |   x <- res0
     |   y <- res1
     | yield
     |   x + y
     |
val res2:
  cats.data.IndexedStateT[cats.Eval, (Int, Double, LazyList[Double]),
    (Int, Double, LazyList[Double]), Double] = cats.data.IndexedStateT@37079700

scala> inf().take(10).foldLeft(res2.run((0, Double.NaN, inf()))) { case (state, _) => res2.run(state.value._1) }
2.0
5.0
8.0
11.0
14.0
17.0
val res3: cats.Eval[((Int, Double, LazyList[Double]), Double)] = cats.Eval$$anon$1@1a19727e
```

---

The next method `transformF` is possible because the result from `run` - of type `F[(SB, A)]` - can be "forgotten" the
structure (pairing and effect) of, and be just a value of some type `SAʹ`; `(SC, B)` as well - but not the effect `G` - can
be "forgotten" as a value of some type `SBʹ`. Composing `run` with `f`, the `IndexedStateT.apply` method can be invoked on
this "forgetful" function:

```Scala
def transformF[G[_]: Applicative, SC, B](
  f: F[(SB, A)] => G[(SC, B)]
)(implicit F: FlatMap[F]): IndexedStateT[G, SA, SC, B] =
  IndexedStateT.apply(run andThen f)
```

Methods from the companion object
---------------------------------

There are four companion objects, `State`, `StateT`, `IndexedState` and `IndexedStateT`, but only the latter is defined in
the same file as the companion `class`, whereas the other three `object`s are defined together with their respective type
alias in `cats/data/package.scala`.

There are two `apply*` methods in the companion object `IndexedStateT`:

```Scala
def apply[F[_], SA, SB, A](f: SA => F[(SB, A)])(implicit F: Applicative[F]): IndexedStateT[F, SA, SB, A] =
  applyF(F.pure(f))

def applyF[F[_], SA, SB, A](runF: F[SA => F[(SB, A)]]): IndexedStateT[F, SA, SB, A] =
  new IndexedStateT(runF)
```

The `apply` method resorts to `applyF` using an `F: Applicative[F]` typeclass instance, to lift the function parameter
`f: SA => F[(SB, A)]` into `F`; the latter is then a straight instantiating of `IndexedStateT`.

`IndexedState` object has a method `apply`:

```Scala
def apply[S1, S2, A](f: S1 => (S2, A)): IndexedState[S1, S2, A] =
  IndexedStateT.applyF(Now(f andThen Now.apply))
```

which uses `cats.Eval` as effect, specifically the eager `Eval.Now` (obviously, there is no need for laziness when the pure
value is a _function_).

### `State` methods

`State` object has a method `apply` that is just an alias for the above:

```Scala
def apply[S, A](f: S => (S, A)): State[S, A] = IndexedState.apply(f)
```

`State` can have a typeclass instance of the `Applicative` typeclass because of the `pure` method, which lifts an anonymous
function that maintains state and outputs `a: A`:

```Scala
def pure[S, A](a: A): State[S, A] = State(_ -> a)
```

A parameterless method is `empty` which resorts to `pure` when given a `Monoid[A]`:

```Scala
def empty[S, A: Monoid]: State[S, A] = pure(Monoid[A].empty)
```

Using a function parameter, the `modify` and `inspect` methods create, respectively, `State`s that modify the state but not
the `Unit` output, and `State`s that keep the same state and thus always also return "the same" - although applied - output:

```Scala
def modify[S](f: S => S): State[S, Unit] = State(f(_) -> ())
def inspect[S, T](f: S => T): State[S, T] = State(s => (s, f(s)))
```

Not to apply a function for the output, `get` is an alias for `inspect` with `identity` as function argument, whereas not to
apply a function to a (thus constant) state, `set` is an alias for `modify` with a constant function argument:

```Scala
def get[S]: State[S, S] = inspect(identity)
def set[S](s: S): State[S, Unit] = modify(_ => s)
```

### `IndexedStateT` and `StateT` methods

The methods in the (companion) objects `IndexedStateT` and `StateT` have the same nomenclature and identical implementations:
the only difference is typing: the former has two distinct type parameters `SA` and `SB` for the state, while the latter has
only one type parameter `S`.

The `applyF` methods delegate to `IndexedStateT.applyF`:

```Scala
def applyF[F[_], SA, SB, A](runF: F[SA => F[(SB, A)]]): IndexedStateT[F, SA, SB, A] =
  IndexedStateT.applyF(runF)

def applyF[F[_], S, A](runF: F[S => F[(S, A)]]): StateT[F, S, A] =
  IndexedStateT.applyF(runF)
```

```Scala
def apply[F[_], SA, SB, A](f: SA => F[(SB, A)])(implicit F: Applicative[F]): IndexedStateT[F, SA, SB, A] =
  applyF(F.pure(f))

def apply[F[_], S, A](f: S => F[(S, A)])(implicit F: Applicative[F]): StateT[F, S, A] =
  applyF(F.pure(f))
```

The function parameter of the `modifyF` methods lift the result into `F`, and delegate to the above `apply` methods, without
having an output (`Unit`); with some hints from the ascriptions `F.lift(_ -> ()): F[SB] => F[(SB, Unit)]`, respectively,
`F.lift(_ -> ()): F[S] => F[(S, Unit)]`, their implementations are:

```Scala
def modifyF[F[_], SA, SB](f: SA => F[SB])(implicit F: Applicative[F]): IndexedStateT[F, SA, SB, Unit] =
  apply(f andThen F.lift(_ -> ()))

def modifyF[F[_], S](f: S => F[S])(implicit F: Applicative[F]): StateT[F, S, Unit] =
  apply(f andThen F.lift(_ -> ()))
```

The `modify` methods delegate to the above `modifyF` methods, composing the function parameter with `F.pure`, such that the
result is lifted into the `Applicative` `F`:

```Scala
def modify[F[_], SA, SB](f: SA => SB)(implicit F: Applicative[F]): IndexedStateT[F, SA, SB, Unit] =
  modifyF(f andThen F.pure)

def modify[F[_], S](f: S => S)(implicit F: Applicative[F]): StateT[F, S, Unit] =
  modifyF(f andThen F.pure)
```

The `setF` methods are aliases for the `modifyF` methods, passing as function argument the constant function (so the state
is "modified" to itself):

```Scala
def setF[F[_], SA, SB](fsb: F[SB])(implicit F: Applicative[F]): IndexedStateT[F, SA, SB, Unit] =
  modifyF(_ => fsb)

def setF[F[_], S](fs: F[S])(implicit F: Applicative[F]): StateT[F, S, Unit] =
  modifyF(_ => fs)
```

The `set` methods delegate to the above `setF` methods, lifting a constant state into the `Applicative` `F`:

```Scala
def set[F[_], SA, SB](sb: SB)(implicit F: Applicative[F]): IndexedStateT[F, SA, SB, Unit] =
  setF(F.pure(sb))

def set[F[_], S](s: S)(implicit F: Applicative[F]): StateT[F, S, Unit] =
  setF(F.pure(s))
```

So, `modify*` allow the state to be modified, but `State`s have no output, whereas `set*` return `State`s that both keep a
constant state and have no output.

---

Another set of common methods to both `IndexedStateT` and `StateT` are `pure`,  `liftF`, `inspect`, `inspectF`, `get`, and
`fromState`. The difference from [`State` methods](#state-methods) is that this set has an effect `F[_]` parameter, while the
resemblance is that they have still just one state type parameter `S`. At the base of these methods is `inspectF` (hence,
there is no `set` method):

```Scala
def inspectF[F[_], S, A](f: S => F[A])(implicit F: Applicative[F]): IndexedStateT[F, S, S, A] =
  IndexedStateT.apply(s => F.map(f(s))(s -> _))
```

which passes the function literal `s => F.map(f(s))(s -> _)` of type `S => F[(S, A)]` to the `IndexedStateT.apply` method
(where it is lifted into the `Applicative` `F`). It keeps the same state and thus always also returns "the same" - although
applied - output.

The `inspect` method resort to `inspectF`, passing it the function `f` with result lifted into the `Applicative` `F`:

```Scala
def inspect[F[_], S, A](f: S => A)(implicit F: Applicative[F]): IndexedStateT[F, S, S, A] =
  inspectF(f andThen F.pure)
```

Not to apply a function for the output, `get` is an alias for `inspect` with `identity` as function argument:

```Scala
def get[F[_]: Applicative, S]: IndexedStateT[F, S, S, S] =
  inspect(identity)
```

The methods `pure` and `liftF` build a constant function from their, respective, arguments `a: A` and `fa: F[A]`, passing it
to, respectively, `inspect` and `inspectF`:

```Scala
def pure[F[_]: Applicative, S, A](a: A): IndexedStateT[F, S, S, A] =
  inspect(_ => a)
def liftF[F[_]: Applicative, S, A](fa: F[A]): IndexedStateT[F, S, S, A] =
  inspectF(_ => fa)
```

The only sealed usage of the `IndexedStateT#transformF` is in the method `fromState`:

```Scala
def fromState[F[_], S, A](s: State[S, F[A]])(implicit F: Applicative[F]): StateT[F, S, A] =
  s.transformF { lsfa =>
    val (sʹ, fa) = lsfa.value
    F.map(fa)((sʹ, _))
  }
```

with a `State` parameter `s: State[S, F[A]]`, where `F[_]: Applicative` is another effect, besides `Eval` (recall that
`State[S, A]` is just a type alias for `IndexedStateT[Eval, S, S, A]`). So the output here is an effect `F[A]`. Invoking the
`transformF` method on the receiver `s`, with argument the block with function parameter `lsfa`, the latter, when invoked,
assigns the `Eval#value` of `lsfa: Eval[(S, F[A])]` to temporary values `sʹ: S` and `fa: F[A]`; then, `F.map` is invoked to
lift not just `a: A` but the pair `(sʹ: S, a: A)` into `F`.

Exercise 08.6
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

lazy val list: LazyList[Unit] = () #:: list
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
      x.toInt
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

lazy val list: LazyList[Unit] = () #:: list

println {
  list.take(3).foldLeft(Left(x): Expr[Double] Either Tree[Double]) {
    case (Left(xa), _)  => Right(expr.run(xa).value._1)
    case (Right(ta), _) => Left(tree.run(ta).value._1)
  }.right.get
}
```

Solution - Part 3
-----------------

The difference is that when _fluctuating_, `expr` and `tree` must alternate, depending on which are the first state and last
state.

For, suppose we have the following translation of the above `for` comprehension:

```Scala
expr.flatMap[Tree[Double], Int] { _ =>
  tree.flatMap[Tree[Double], Int] { _ =>
    expr.map[Int] { x =>
      x.toInt
    }
  }
}
```

The final state has type `Tree[Double]` while the output has type `Int`, and so these are the "flexible" type parameters `SC`
and `B` in `flatMap`. However, to see why `expr` and `tree` _must_ alternate, we can extract the value used in each nested
level (`0` for outermost, `2` for innermost), and also ascribe types to the receivers:

```Scala
val x2: IndexedState[Expr[Double], Tree[Double], Int] = (expr: IndexedState[Expr[Double], Tree[Double], Double]).map { x =>
  x.toInt
}

val t1: IndexedState[Tree[Double], Tree[Double], Int] = (tree: IndexedState[Tree[Double], Expr[Double], Double]).flatMap { _ =>
  x2: IndexedState[Expr[Double], Tree[Double], Int]
//                 1st1st1st1st                                                           2nd2nd2nd2nd
}

val x0: IndexedState[Expr[Double], Tree[Double], Int] = (expr: IndexedState[Expr[Double], Tree[Double], Double]).flatMap { _ =>
  t1: IndexedState[Tree[Double], Tree[Double], Int]
//                 1st1st1st1st                                                           2nd2nd2nd2nd
}
```

The point (5) in the discussion of `flatMap` mandates that the types marked with `1st` and `2nd` must coincide (otherwise,
`flatMap` is impossible to be implemented).

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-6-WriterT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)
