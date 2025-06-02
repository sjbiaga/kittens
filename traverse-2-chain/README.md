[First](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/traverse-3-lazylist/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md)

Lesson 07: Traversable (cont'd)
===============================

`Traverse[Chain]`
-----------------

We quote from the `documentation` on [`Chain`](https://typelevel.org/cats/datatypes/chain.html) in package `cats.data`:

    Chain is an immutable sequence data structure that allows constant time prepending, appending and concatenation.

`Cats` provides a typeclass instance of the `Traverse` typeclass for `Chain` as the value `catsDataInstancesForChain` right
in its companion object:

```Scala
package cats
package data

object Chain {
  implicit val catsDataInstancesForChain: Traverse[Chain] & ... =
    new Traverse[Chain] with ... {
      def traverse[G[_], A, B](fa: Chain[A])(f: A => G[B])(implicit G: Applicative[G]): G[Chain[B]] =
        if (fa.isEmpty) G.pure(Chain.nil)
        else
          G match {
            case x: StackSafeMonad[G] => Traverse.traverseDirectly(fa.iterator)(f)(x)
            case _ => ... // see traverseViaChain
          }
    }
}
```

The implementation is identical with `catsStdInstancesForList` from
[`Traverse[List]`](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md#traverselist), except that it does
not have to convert to and from `Chain`, because `Traverse.traverseDirectly` and `Chain.traverseViaChain` work directly on
`Chain`s (only half true). `Chain` is not an `IterableOnce`, but its `Iterator` is (resorting to a `private`
access `ChainIterator` class).

We [already](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md#traverselist) discussed
`Traverse.traverseDirectly`, so let us focus on the other branch in the pattern matching with `G` as selector:

```Scala
package cats
package data

object Chain {
  def traverseViaChain[G[_], A, B](
    as: immutable.IndexedSeq[A]
  )(f: A => G[B])(implicit G: Applicative[G]): G[Chain[B]] = ???
}
```

In `traverseViaChain` - a brilliant example in the use of `Eval` -, the original collection arrives already packed into an
immutable `IndexedSeq[A]` - even if called from `Chain` directly. It operates with _ranges_ - of maximum `width` (128) size,
in the base case - from the original collection `as`.

There are two cases - in either case, there is a separate iterative `while` loop to:

1. process a range of at most `width` elements;

1. process an unlimited number of successive sub-ranges.

1. Case (2) reverts to case (1) in repeated calls to a nested method `loop` of type `Eval[G[Chain[B]]]`; this method is also
   recursive in the case (2). A key observation is that the `Eval` type is used _both_ as the return type of, _and_ as the
   second parameter type to `G.map2Eval` invocations: this allows variables like `flist` or `fchain` below (lifted to `Eval`)
   to be used both as left hand side in assignments involving, and in (second) parameter passing to `G.map2Eval`.

[The `Eval` companion object has an `evaluate` method, which runs in a `@tailrec`ursive `loop` a _program_ or _compilation_
through `Eval`s:

```Scala
object Eval {
  private def evaluate[A](e: Eval[A]): A = ???
}
```

Any code can be of type `A`: in our case, because `G` is a context too, `A` is either `G[List[B]]` or `G[Chain[B]]` and
`evaluate` involves invoking `G.map2Eval`. The thing with `Applicative#map2Eval` is that it _returns_ an `Eval` object which
_depends_ on its parameters, and this occurs (on behalf of another `Eval` - `flatMap`ped or `defer`red) _whilst_ `evaluate`
is executing: this `Eval` then gets used further.

Thus, more importantly is that the program - having already been compiled (as a `G[Chain[B]]`) - continues to _alter_ itself,
depending on the parameters to `G.map2Eval` (stuff on the heap is appended): especially, `Applicative`s with _fail fast_
semantics can _short circuit_ and terminate the program simply by _not using_ the second argument - if they need, they can
return `Eval.now(<failure>)`.]

So, let us discuss the processing, in each case.

1. Starting from the `end` of each range, its implementation is a lazy "foldRight" disguised as an iterative `while` loop.

- Given `start` and `end` are the indices of a range, before iterating, using `a = as(end - 1)`, the processing initializes a
  variable `flist` to program the compilation of an unevaluated singleton in `G`:

```Scala
var flist = Eval.later { G.map(f(a))(_ :: Nil) } // or:
var flist: Eval[G[List[B]]] = Eval.later { G.map(f(a): G[B])((_: B) :: (Nil: List[B])) }
```

- Ranging leftwards (from `end` to `start`, or from _right to left_) by the ever decreasing index `idx`, with each iterative
  step, using `a = as(idx)`, it _compiles_ the "cons" operator (`::`) applied to `f(a)` and the _unevaluated_ list, then
  updates `flist` to program this compilation in `G`:

```Scala
val rhs = flist
flist = Eval.defer { G.map2Eval(f(a), rhs)(_ :: _) } // or:
flist = Eval.defer { G.map2Eval(f(a): G[B], rhs: Eval[G[List[B]]])((_: B) :: (_: List[B])) }
```

- When done, the type of `flist` is changed to the return type of the `loop` method (with `Chain` instead of `List` as nested
  inner type):

```Scala
flist.map(G.map(_)(Chain.fromSeq(_))) // or:
(flist: Eval[G[List[B]]]).map(G.map(_: G[List[B]])(Chain.fromSeq(_: List[B]))): Eval[G[Chain[B]]]
```

2. The results from the calls to the recursive nested `loop` method are "concatenated" (as `Chain`s) but unevaluated,
   in a similar fashion to (1). A "batch size" as `step` is computed simply (which may reach values considerably greater than
   _powers_ of `width` - greater than `math.pow(2, 14)` -, when "size really matters").

- A variable `fchain` is initialized as a program to "pull" an unevaluated first result from (1):

```Scala
var fchain: Eval[G[Chain[B]]] = Eval.defer { loop(start, start + step) }
```

- Looping rightwards, with ranges of size `step`, at start indices ever increasing (or from _left to right_), an intermediary
  stage - in a `while` loop - "pulls" the next unevaluated `Chain` in `G`, compiles the concatenation operator (`++`), then
  updates `fchain` to program this compilation in `G`:

```Scala
val rhs = loop(start, end min start + step)
fchain = fchain.flatMap(G.map2Eval(_, rhs)(_ ++ _)) // or:
fchain = fchain.flatMap(G.map2Eval((_: G[Chain[B]]), rhs: Eval[G[Chain[B]]])((_: Chain[B]) ++ (_: Chain[B])))
```

- The base case (1) will _not_ be the case as long as `step` is greater than `width`: this means that case (2) will divide by
  `width` and recurse - as case (2) again - with exponentially ever smaller ranges.

3. The resulting (with `B` as base type) unevaluated `Chain` compiled in `G` is a compilation that is programmed as well
   through `Eval`s: this _outer_ program is executed in a _stack safe_ manner by calling `Eval#value` upon it.

```Scala
loop(0, as.size).value // or:
loop(0, as.size).value: G[Chain[B]]
```

Invoking `loop` twice
---------------------

The `loop` methods works with any valid range: we could, for example, invoke the algorithm twice, and concatenate the results:

```Scala
{ val half = as.size / 2
  if 0 < half && half < as.size
  then
    for
      fst <- Eval.defer { loop(0, half) }
      snd <- Eval.later { loop(half, as.size) }
      res <- G.map2Eval(fst, snd)(_ ++ _)
    yield
      res
  else
    loop(0, as.size)
}.value
```

Unfolding Case (1)
------------------

Also, we can unfold case (1) to exemplify how it functions. Thus, we have an `Applicative` `G` and a traversal function `f`:

```Scala
import cats.Applicative, cats.Eval, cats.instances.option._

val G = implicitly[Applicative[Option]]

val f: Int => Option[Int] = { n => println(n); Some(n) }
```

Let us suppose that we have a `Chain` with three items _0_ -> `10`, _1_ -> `100`, _2_ -> `1000` - the first three powers of
ten, in increasing order; case (1) of `traverseViaChain` unfolds like this:

```Scala
var flist = Eval.later { // the "start" Eval  // line #01
  println(1)
  G.map(f(1000)) {                            // line #03
    it =>
      println(2)
      it :: Nil
  }
}
flist     = {
  val a = 100
  val rhs1000 = flist
  Eval.defer { // the "first" defer           // line #12
    println(3)
    G.map2Eval(f(a), rhs1000) {               // line #14
      (it, ls) =>
        println(4)
        it :: ls
    }
  }
}
flist     = {
  val a = 10
  val rhs100 = flist
  Eval.defer { // the "last" defer            // line #24
    println(5)
    G.map2Eval(f(a), rhs100) {                // line #26
      (it, ls) =>
        println(6)
        it :: ls
    }
  }
}
flist.map(identity).value                     // line #33
```

The numbers `println`ed are the following: `5`, `10`, `3`, `100`, `1`, `1000`, `2`, `4`, `6`: the _odd_ digits occur in
_decreasing_ order, while the _even_ digits occur in _increasing_ order. The _powers of ten_ occur in _increasing_ order in
the output.

What happens is that the defer corresponding to the leftmost number (`10`) is the last value assigned to `flist`: so, like
the value `a` (bound to `10`) and the function `f`, `rhs100` is _captured_ as part of the _closure_ argument to `G.map2Eval`
(line #26). But this would mean that the "last" defer captures `rhs100`, which captures `rhs1000` (line #14), and so on,
upwards... This is the _heap_ that is built, where the program resides.

Now, line #33 has a little added to it, which yields a `FlatMap(flist, identity andThen Now(_))` object - for uniformity. Upon
the invocation of `Eval#value` (line #33), the "last" defer will be the first to be `evaluate`d: but how can we "pull" it out
of the `FlatMap`?! This will be also the case with the other defers - wrapped inside a `FlatMap`.

Going backwards, the answer is that `flist` - from line #33 - pattern matches a `Defer` instance:

```Scala
FlatMap(Defer { () => <block #24> }, identity andThen Now(_)).value
```

Now this `evaluate` (on behalf of `.value`) can pattern match:

```Scala
({ () => <block #24> }.apply()).flatMap(identity andThen Now(_))
```

It executes the block from line #24, which `println`s `5` and applies `G.map2Eval` to `f(a)` and `rhs100`, `println`ing 10.
Because `f` yields `Some(10)` and the method invoked is `Applicative[Option].map2Eval`, the `Eval` program `rhs100` (as
second parameter named "`lfb`") will be _altered_:

```Scala
lfb.map { // or: rhs100.map
  case Some(b) => Some(f2(10, b)): Option[List[Int]]
  case None    => None
}: Eval[Option[List[Int]]]
```

---

Because the function parameter `f2` stands for the binary function in line #26, and assuming there wiil be no fail fast, we
could rewrite the above case as:

```Scala
lfb.map { b => Some(<function-block #26>(10, b.get)) }
```

or further - turning `b` into a placeholder:

```Scala
lfb.map { (_.get) andThen <function-block #26>(10, _) andThen Option.apply }
```

which - dropping `Option.apply` (but remembering to add it back) and leaving just one placeholder (albeit that does not
compile) - we could abbreviate as:

```Scala
<function-block #26>(10, _.get)
```

---

In other words, the heap now looks like this:

```Scala
FlatMap(rhs100, <function-block #26>(10, _.get) andThen Now(_))
  .flatMap(identity andThen Now(_))
```

The `flatMap` method intervenes before looping in `evaluate`:

```Scala
FlatMap(FlatMap(rhs100
               , <function-block #26>(10, _.get) andThen Now(_))
       , identity andThen Now(_))
```

Now this `evaluate` can pattern match (and continue to loop):

```Scala
FlatMap(rhs100
       , (<function-block #26>(10, _.get) andThen Now(_))
           .flatMap(identity andThen Now(_)))
```

`rhs100` is the "first" defer:

```Scala
FlatMap(Defer { () => <block #12> }
       , (<function-block #26>(10, _.get) andThen Now(_))
           .flatMap(identity andThen Now(_)))
```

Same as before, `evaluate` can pattern match:

```Scala
({ () => <block #12> }.apply()).flatMap((<function-block #26>(10, _.get) andThen Now(_))
                                          .flatMap(identity andThen Now(_))
                                       )
```

When this function is applied, the block from line #12 `println`s `3` and applies `G.map2Eval` to `f(a)` and `rhs1000`,
`println`ing `100`. Because `f` yields `Some(100)` and the method invoked is `Applicative[Option].map2Eval`, the `Eval`
program `rhs1000` will be _altered_ - disguised as an `Eval#map` directed to `Eval#flatMap` and instantiated as a `FlatMap`:

```Scala
FlatMap(rhs1000
       , <function-block #14>(100, _.get) andThen Now(_))
  .flatMap((<function-block #26>(10, _.get) andThen Now(_))
             .flatMap(identity andThen Now(_)))
```

The `flatMap` method intervenes before looping in `evaluate`:

```Scala
FlatMap(FlatMap(rhs1000
               , <function-block #14>(100, _.get) andThen Now(_))
       , (<function-block #26>(10, _.get) andThen Now(_))
           .flatMap(identity andThen Now(_)))
```

Now this `evaluate` can pattern match (and continue to loop):

```Scala
FlatMap(rhs1000
       , (<function-block #14>(100, _.get) andThen Now(_))
           .flatMap((<function-block #26>(10, _.get) andThen Now(_))
                      .flatMap(identity andThen Now(_))))
```

`rhs1000` is the "start" `Eval`:

```Scala
FlatMap(Later { <block #01> }
       , (<function-block #14>(100, _.get) andThen Now(_))
           .flatMap((<function-block #26>(10, _.get) andThen Now(_))
                      .flatMap(identity andThen Now(_))))
```

Similar as before (but with `Later` instead of `Defer`), `evaluate` can pattern match:

```Scala
((<function-block #14>(100, _.get) andThen Now(_)).apply(<block #01>))
   .flatMap((<function-block #26>(10, _.get) andThen Now(_))
              .flatMap(identity andThen Now(_)))
```

Executing the "block from line #01", it `println`s `1`, invokes `f(1000)` - which `println`s `1000` - and yields `Some(1000)`.
The method `Option#map` is invoked with the latter receiver, which will pass `1000` to the `it` parameter to the block from
line #03: this will `println` `2` and perform the _first_ "cons" operation, yielding `1000 :: Nil`, lifted in `G`/`Option`.

The resulting `List` lifted in `G` will be applied:

```Scala
((<function-block #14>(100, _.get) andThen Now(_)).apply(Some(1000 :: Nil)))
   .flatMap((<function-block #26>(10, _.get) andThen Now(_))
              .flatMap(identity andThen Now(_)))
```

1. block from line #14: this will `println` `4` and perform the _second_ "cons" operation, yielding `100 :: (1000 :: Nil)`,
   lifted in `G`, lifted in `Eval`:

```Scala
Now(Some(100 :: 1000 :: Nil))
  .flatMap((<function-block #26>(10, _.get) andThen Now(_))
             .flatMap(identity andThen Now(_)))
```

which compiles to:

```Scala
FlatMap(Now(Some(100 :: 1000 :: Nil))
       , (<function-block #26>(10, _.get) andThen Now(_))
           .flatMap(identity andThen Now(_)))
```

Now this `evaluate` can pattern match (and continue to loop):

```Scala
((<function-block #26>(10, _.get) andThen Now(_)).apply(Some(100 :: 1000 :: Nil)))
   .flatMap(identity andThen Now(_))
```

2. block from line #26: this will `println` `6` and perform the _third_ "cons" operation,
   yielding `10 :: (100 :: (1000 :: Nil))`, lifted in `G`, lifted in `Eval`:

```Scala
Now(Some(10 :: 100 :: 1000 :: Nil))
  .flatMap(identity andThen Now(_))
```

which compiles to:

```Scala
FlatMap(Now(Some(10 :: 100 :: 1000 :: Nil))
       , identity andThen Now(_))
```

Now this `evaluate` can pattern match (and continue to loop):

```Scala
(identity andThen Now(_)).apply(Some(10 :: 100 :: 1000 :: Nil))
```

3. `evaluate`ing `Now(Some(10 :: 100 :: 1000 :: Nil))`, it ends with `Some(10 :: 100 :: 1000 :: Nil): Option[List[Int]]`.

4. Let us assume otherwise that - at some point - `block #01` returned `None`:

```Scala
((<function-block #14>(100, _.get) andThen Now(_)).apply(None))
   .flatMap((<function-block #26>(10, _.get) andThen Now(_))
              .flatMap(identity andThen Now(_)))
```

This further reduces to:

```Scala
Now(None)
   .flatMap((<function-block #26>(10, _.get) andThen Now(_))
              .flatMap(identity andThen Now(_)))
```

which compiles to:

```Scala
FlatMap(Now(None)
       , (<function-block #26>(10, _.get) andThen Now(_))
           .flatMap(identity andThen Now(_)))
```

which evaluates to:

```Scala
((<function-block #26>(10, _.get) andThen Now(_)).apply(None))
   .flatMap(identity andThen Now(_))
```

which reduces to:

```Scala
Now(None).flatMap(identity andThen Now(_))
```

which compiles to:

```Scala
FlatMap(Now(None), identity andThen Now(_))
```

which evaluates to:

```Scala
Now(None)
```

and to `None`: this is the fail fast semantics; the heap is built, yet, no matter how big it had gotten, it _must_ be reduced
without omitting intermediary but trivial compilations or evaluations.

[First](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/traverse-3-lazylist/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md)
