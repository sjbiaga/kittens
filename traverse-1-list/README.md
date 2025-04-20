[Previous](https://github.com/sjbiaga/kittens/blob/main/nat-4-list/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/traverse-2-chain/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md)

Lesson 07: Traversable
======================

The `map` method inherited from the `Functor` trait is implemented with a `traverse`al using the `cats.Id` monad (thus also
with an instance of `Applicative[Id]`).

```Scala
package cats

trait Traverse[F[_]] extends Functor[F] {
  def traverse[G[_]: Applicative, A, B](fa: F[A])(f: A => G[B]): G[F[B]]

  def map[A, B](fa: F[A])(f: A => B): F[B] =
    traverse[Id, A, B](fa)(f)

  ...
}
```

The idea behind the `traverse` method is that it iterates through the `fa`'s, and for each `a: A` it invokes `f`; now, `f(a)`
is a `G[B]`, and - because `G` is a `Functor` - `G.map(f(a))(h)` can be used, where `h: <B> => F[B]` is a _collect_ function,
usually in the "_accumulator_" form `k: (B, F[B]) => F[B]` (right) or `kʹ: (F[B], B) => F[B]` (left). `G` is an `Applicative`
(a subtype of `Functor`) for a reason: the collection might be _initialized_ as empty, for example, via `G.pure(F.empty[B])`
(if `F` had such method).

The `Applicative[G[_]]` trait has - inherited from the `Apply[G]` trait - a method `map2` as well as a method `map2Eval` for
these two ([initializing and] accumulating) purposes, defined in terms of `map` and (indirectly via `product`) `ap`:

```Scala
package cats

trait Apply[G[_]] extends ... {
  override def product[A, B](ga: G[A], gb: G[B]): G[(A, B)] =
    ap(map(ga)(Tuple2.apply[A, B].curried))(gb)  // line #a

  def map2[A, B, Z](ga: G[A], gb: G[B])(f: (A, B) => Z): G[Z] =
    map(product(ga, gb))(f.tupled)               // line #b

  def map2Eval[A, B, Z](ga: G[A], lgb: Eval[G[B]])(f: (A, B) => Z): Eval[G[Z]] =
    lgb.map(map2(ga, _)(f))                      // line #c
}
```

`Tuple2.apply[A, B].curried` is just the function `f: A => (B => (A, B)) = { (a: A) => ((b: B) => (a, b): (A, B)) }`, and - as
it is the second parameter to `map(ga)(#2)` -, line #a:

```Scala
ap(map(ga)(Tuple2.apply[A, B].curried))(gb)
//         ^^^^^^^^^^^^^^^^^^^^^^^^^^
//         second parameter to map, a
//         function f: A => (B => (A, B))
//                           ^^^^^^^^^^^
//                           function h
```

actually rewrites as:

```Scala
ap(gh)(gb) // or:
ap(gh: G[B => (A, B)])(gb: G[B]): G[(A, B)]
```

where `gh` is `map(ga)(f)` or `map(ga) { a => f(a) }`, where `f(a) = h: B => (A, B)`.

In line #b, the first and second parameters to `map(#1)(#2)` are `product(ga, gb): G[(A, B)]` and `f.tupled: ((A, B)) => Z`:
`f` is a function of two parameters, whereas `map` expects a unary function as second argument. So the typed signature in the
use of `map` is `map(gab: G[(A, B)])(fʹ: ((A, B)) => Z): G[Z]`, or `map(gab: G[Tuple2[A, B]])(fʹ: Tuple2[A, B] => Z): G[Z]`,
where `fʹ = f.tupled` is the unary version of the binary function `f`.

The difference between `map2` and `map2Eval` is that the latter is _lazy_: line #c _compiles_ the direct use of `map2` in the
language of `Eval` - which is trampolined, and thus - lazily interpreted. This means that there is no `G[Z]` _value_ until
`Eval#value` method is called.

But let us look at some instances of the typeclass `Traverse[F[_]]` in `Cats`' package `cats.instances`.

`Traverse[List]`
----------------

`List` is most common and, for it, there are typeclass instances of many typeclasses - among which, `Traverse`:

```Scala
package cats

package object instances {
  object list {
    implicit val catsStdInstancesForList: Traverse[List] & ... =
      new Traverse[List] with ... {
        def traverse[G[_], A, B](fa: List[A])(f: A => G[B])(implicit G: Applicative[G]): G[List[B]] =
          if (fa.isEmpty) G.pure(Nil)                                          // line #08
          else
            G match {
              case x: StackSafeMonad[G] =>
                x.map(Traverse.traverseDirectly[G, A, B](fa)(f)(x))(_.toList)  // line #11
              case _ =>
                // see Chain.traverseViaChain                                  // line #12
            }
      }
  }
}
```

For an empty `List`, the result is `Nil` lifted in the applicative `G[_]` - line #08. Otherwise, the implementation does
(surprisingly or not) revert to a stack safe implementation:

1. a `Chain.traverseViaChain` is chosen - line #12 -, because `Chain` has concatenation (`++`) with `O(1)` complexity,
   see [`Traverse[Chain]`](https://github.com/sjbiaga/kittens/blob/main/traverse-2-chain/README.md#traversechain);

1. unless `G` were a `StackSafeMonad` - line #11 -, in which case `Traverse.traverseDirectly` is preferred - available for
   subtypes of `IterableOnce[A]`, a base trait for `Option` and `scala.collection`s (being a supertrait of `Iterable[A]`);
   appending (`:+`) for a `Chain` has also `O(1)` complexity:

```Scala
package cats

object Traverse {
  private[cats] def traverseDirectly[G[_], A, B](
    fa: IterableOnce[A]
  )(f: A => G[B])(implicit G: StackSafeMonad[G]): G[Chain[B]] =
    fa.iterator.foldLeft(G.pure(Chain.empty[B])) { (accG, a) =>
      G.map2(accG, f(a))(_ :+ _)
    }
}
```

Many types from Scala collections choose to `traverseDirectly` via a `Chain` when the `Applicative` is a `StackSafeMonad`.
Aside being said, two things stand in opposition to one another:

1. `foldLeft` does eager accumulation, but cannot be used together with a `prepend` (`O(1)`) operator;

1. `foldRight` requires lazy accumulation, yet is to be used together with a `prepend` operator.

Of course, lazy accumulation is slower and heavier, versus the use of `prepend` which may be faster.

That is how `traverseDirectly` was born: it dropped `foldRight` and chose `Chain` as an intermediary collection for the
result: but it requires the collection to be converted to (before the traversal) and from (after the traversal) a `Chain`.

The dual `traverseViaChain` method, on the other hand, chose lazy accumulation mixed with _both_ pseudo-foldRight traversal
using a `List` and `prepending`, _and_ pseudo-foldLeft traversal using a `Chain` and concatenation.

`Traverse[List]` - via `Eval`
-----------------------------

Let us see some examples of traversing eagerly a `List[Int]` via the `Eval` `StackSafeMonad` - which provides for laziness.
We can observe the differences between `Eval.always`, `Eval.later` and `Eval.now`. The traversal function doubles each item
in the list, which it also `println`s, but this depends on the memoization chosen:

```scala
scala> List(1,2,3,4).traverse { it => Eval.always { println(it); it * 2 } }
val res0: cats.Eval[List[Int]] = cats.Eval$$anon$1@1e275478

scala> res0.value
1
2
3
4
val res1: List[Int] = List(2, 4, 6, 8)

scala> res0.value
1
2
3
4
val res2: List[Int] = List(2, 4, 6, 8)
```

`Eval.always` will not memoize its argument - which is why the list items are printed each time `value` is invoked on `res1`.
This entails, of course, that its parameter is _call-by-name_. Another intriguing question, perhaps, is where does "all this
information" about what to `println` reside in-between invocations? The answer is a rhetoric question: how could `res1.value`
print lines unless the _program_ `res1` were compiled, residing where else but on heap?!

The parameter of `Eval.now` is _call-by-value_, which is why the items are `println`ed upon traversal:

```scala
scala> List(1,2,3,4).traverse { it => Eval.now { println(it); it * 2 } }
1
2
3
4
val res3: cats.Eval[List[Int]] = cats.Eval$$anon$1@4f1502d7

scala> res3.value
val res4: List[Int] = List(2, 4, 6, 8)

scala> List(1,2,3,4).traverse { it => Eval.later { println(it); it * 2 } }
val res5: cats.Eval[List[Int]] = cats.Eval$$anon$1@685edb96

scala> res5.value
1
2
3
4
val res6: List[Int] = List(2, 4, 6, 8)

scala> res5.value
val res7: List[Int] = List(2, 4, 6, 8)
```

`Eval.later` works like `Eval.always`, with distinction on memoization: the first time `res5.value` is invoked, the
`call-by-name` parameter turned into a `thunk` (closure) is evaluated, and the items are `println`ed then (unlike `Eval.now`).
The results are memoized, and on the second invocation, the items are no longer `println`ed - which means the thunks are no
longer evaluated (unlike `Eval.always`); this is achieved in the `Eval.Later[+A]` `case class` by overriding `def value: A`
as `lazy val value: A`.

`Traverse[List]` - via `Chain`
------------------------------

Lazy traversal via `Chain.traverseViaChain` allows also the `Applicative`s to _fail fast_: `map2Eval` is eager in the first
argument, so it may short circuit the second `Eval` parameter, and return `Eval.now(<failure>)` once it entered failed state
(omitting the alteration of the program through the second - compilation in `Eval` - parameter).

As an example, traversing a list with `Option` would return the original list wrapped in `Some`, unless for at least one item
in the original list, the traversing function returned `None`:

```scala
scala> import cats.instances.option._, cats.syntax.traverse._

scala> List(1,2,3,4,5).traverse { it => if it % 4 != 0 then { println(it); Some(it) } else None }
1
2
3
val res8: Option[List[Int]] = None
```

Item `5` is not `println`ed because of how `map2Eval` is implemented in the `Applicative` typeclass instance for `Option`
(line #n below):

```Scala
package cats
package instances

object option {
  implicit val catsStdInstancesForOption: Applicative[Option] & ... =
    new Applicative[Option] with ... =
      override def map2Eval[A, B, Z](fa: Option[A], lfb: Eval[Option[B]])(f: (A, B) => Z): Eval[Option[Z]] =
        fa match {
          case None => Eval.Now(None)        // line #n
          case Some(a) =>
            lfb.map {                        // further compilation in Eval
              case Some(b) => Some(f(a, b))
              case None    => None
            }
        }
}
```

In line #n above, there is no mention of the `lfb` `Eval` - hence, the termination.

Type `A` is `Int`, while `B` and `Z` in this case are both `List[Int]`.

Function `f` is either the "cons" (`::`) operator on `List`s or the concatenation operator (`++`) on `Chain`s.

However, the `Applicative` may also choose to collect _all_ failures, in a typeclass instance for the `Semigroup` typeclass,
for instance `Semigroup[Vector[Int]]` - the case of `Validated`:

```scala
scala> import cats.data.Validated, Validated. { valid, invalid }, cats.instances.vector._

scala> List(1,2,3,4,5).traverse { it => if it % 4 == 0 then valid(it) else { println(it); invalid(Vector(it)) } }
1
2
3
5
val res9: cats.data.Validated[Vector[Int], List[Int]] = Invalid(Vector(1, 2, 3, 5))
```

All items except `4` are `println`ed because of how `map2Eval` is implemented - by default - in `Apply` (in terms of
`Apply#map` and `Apply#product` - via `Apply#map2`) and of how `ValidatedApplicative#map` (line #m below) and
`ValidatedApplicative#product` (line #p below) are implemented (indirectly) in the typeclass instance of the `Applicative`
typeclass for `Validated`:

```Scala
package cats
package data

object Validated {

  implicit def catsDataApplicativeErrorForValidated[E: Semigroup]: Applicative[Validated[E, *], E] & ... =
    new ValidatedApplicative[E] with ... { ... }

  private[data] class ValidatedApplicative[E: Semigroup] extends ... {
    override def map[A, B](fa: Validated[E, A])(f: A => B): Validated[E, B] =
      fa.map(f)                                 // line #m

    override def product[A, B](fa: Validated[E, A], fb: Validated[E, B]): Validated[E, (A, B)] =
      fa.product(fb)(implicitly[Semigroup[E]])  // line #p
  }

}
```

The `Validated#map` method has a _fail fast_ semantics - like `Option` and `Either` - (line #m below), whereas the
`Validated#product` method `combine`s two failed states through a `Semigroup` (line #p below):

```Scala
package cats
package data

sealed abstract class Validated[+E, +A] extends ... {

  def map[B](f: A => B): Validated[E, B] =
    this match {
      case i @ Invalid(_) => i                                         // line #m
      case Valid(a)       => Valid(f(a))
    }

  def product[EE >: E : Semigroup, B](fb: Validated[EE, B]): Validated[EE, (A, B)] =
    val EE = implicitly[Semigroup[EE]]
    (this, fb) match {
      case (Valid(a), Valid(b))       => Valid((a, b))
      case (Invalid(e1), Invalid(e2)) => Invalid(EE.combine(e1, e2))   // line #p
      case (e @ Invalid(_), _)        => e
      case (_, e @ Invalid(_))        => e
    }

}
```

`Traverse[[A] =>> Tuple2[X, A]]`
--------------------------------

Sometimes there is no need of iterating, or a straighter way can be found, as is the case of `Tuple2[X, _]` (pairs), which
just destructures the tuple `fxa: (X, A)`, prior to mapping the second component in the tuple through `f`: this and the first
component are restructured as a pair by `G.map`.

```Scala
package cats

package object instances {
  object tuple {
    def catsStdInstancesForTuple2[X]: Traverse[[A] =>> Tuple2[X, A]] & ... =
      new Traverse[[A] =>> Tuple2[X, A]] with ... {
        def traverse[G[_], A, B](fxa: (X, A))(f: A => G[B])(implicit G: Applicative[G]): G[(X, B)] = {
          val (x, a) = fxa
          G.map(f(a))((x, _))
        }
      }
  }
}
```

(Note that `catsStdInstancesForTuple2` is not implicit because it is deprecated.)

Exercise 07.1
-------------

Give an implementation as a typeclass instance of the `Traverse` typeclass for a higher than two tuple type.

Solution
--------

We present an implementation as a typeclass instance of the `Traverse` typeclass for `Tuple5[W, X, Y, Z, _]`:

```Scala
def kittensTuple5Traverse[W, X, Y, Z]: Traverse[[A] =>> Tuple5[W, X, Y, Z, A]] =
  new Traverse[[A] =>> Tuple5[W, X, Y, Z, A]] {
    def traverse[G[_], A, B](fwxyza: (W, X, Y, Z, A))(f: A => G[B])(implicit G: Applicative[G]): G[(W, X, Y, Z, B)] = {
      val (w, x, y, z, a) = fwxyza
      G.map(f(a))((w, x, y, z, _))
    }
    override def foldLeft[A, B](fwxyza: (W, X, Y, Z, A), b: B)(f: (B, A) => B): B =
      f(b, fwxyza._5)
    override def foldRight[A, B](fwxyza: (W, X, Y, Z, A), lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
      f(fwxyza._5, lb)
  }
```

[Previous](https://github.com/sjbiaga/kittens/blob/main/nat-4-list/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/traverse-2-chain/README.md)
