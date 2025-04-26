[Previous](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-2-EitherT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md)

Lesson 08: Monad Transformers
=============================

In the previous lessons, we have proceeded mainly by giving typeclass instances - for `Option`, `List`, `Expr` - of various
typeclasses: we could thus use `Cats` _syntax_ for `Functor`, `CoflatMap`, `FlatMap`, `Monad`, or `Traverse`.

Composing typeclasses
---------------------

Now, _some_ of the latter `trait`s contain in their definition a method `compose`, which follows a common pattern to _all_
`trait`s, whose names - let us say - are ranged over by "`Typeclass`":

```Scala
trait Typeclass[F[_]] extends Functor[F] /* e.g. */ { self =>

  <member declarations>

  def compose[G[_]: Typeclass]: Typeclass[[α] =>> F[G[α]]] =
    new ComposedTypeclass[F, G]:
      val F: Typeclass[F] = self
      val G: Typeclass[G] = Typeclass.apply[G]
}

trait ComposedTypeclass[F[_], G[_]] extends Typeclass[[α] =>> F[G[α]]]:
  def F: Typeclass[F]
  def G: Typeclass[G]

  <abstract member definitions>

object Typeclass:
  def apply[F[_]](implicit instance: Typeclass[F]): Typeclass[F] = instance
```

There are three definitions above:

- the `Typeclass` typeclass, which declares its members (some `abstract`), and defines its `compose` method to instantiate

- a `ComposedTypeclass`, which extends `Typeclass[F[G[_]]]`, declares two typeclasses instances `F` and `G`, of `Typeclass`
  typeclass for, respectively, `F[_]` and `G[_]`, and defines inherited abstract members in terms of `F` and `G`;

- the companion object with the `apply` method as syntactic sugar for `implicitly[Typeclass[F]]`.

When we derive a typeclass with new members:

```Scala
trait Typeclassʹ[F[_]] extends Typeclass[F] with ... { self =>

  <new member declarations>

  def compose[G[_]: Typeclassʹ]: Typeclassʹ[[α] =>> F[G[α]]] =
      new ComposedTypeclassʹ[F, G]:
        val F: Typeclassʹ[F] = self
        val G: Typeclassʹ[G] = Typeclassʹ[G]
  }
```

we override `compose` and alter its signature, which is possible because of the _subtyping_ relation between the two
typeclasses.

The hierarchy of `Composed*` `trait`s parallels that of the typeclasses:

```Scala
trait ComposedTypeclassʹ[F[_], G[_]] extends ComposedTypeclass[F, G] with Typeclassʹ[[α] =>> F[G[α]]]:
  def F: Typeclassʹ[F]
  def G: Typeclassʹ[G]

  <new abstract member definitions>
```

while the method `apply` in the companion object is defined invariantly in the same manner:

```Scala
object Typeclassʹ:
  def apply[F[_]](implicit instance: Typeclassʹ[F]): Typeclassʹ[F] = instance
```

If typeclass instances of the `Typeclass` typeclass, for, respectively, `List` and `Option`, were imported, we can obtain a
new typeclass instance of the `Typeclass` typeclass by invoking `compose` on the former with the latter as type parameter:

```scala
scala> import cats.instances.list._, cats.instances.option._, cats.syntax.functor._

scala> Typeclass[List].compose[Option]
val res0: cats.Typeclass[[α] =>> List[Option[α]]] = cats.Typeclass$$anon$1@2f8cb4c9

scala> res0.map(List(Some(1), None))(_ + 1) /* e.g. */
val res1: List[Option[Int]] = List(Some(2), None)

scala> res0.isInstanceOf[Functor[[α] =>> List[Option[α]]]]
val res1: Boolean = true
```

We could invoke - the inherited method - `map` on `res0` because we have extended `Functor`: `res1` is also `true`.

---

`Cats` has several - not too many - `Composed*` `trait`s, all declared in package `cats`, with the `private` access modifier,
within `cats`: let us review a few of them.

1. [`ComposedFunctor`](http://typelevel.org/cats/typeclasses/functor.html#functors-compose):

```Scala
package cats

private[cats] trait ComposedFunctor[F[_], G[_]] extends Functor[λ[α => F[G[α]]]] with ... {
  def F: Functor[F]
  def G: Functor[G]

  override def map[A, B](fga: F[G[A]])(f: A => B): F[G[B]] =
    F.map(fga)(G.lift(f))
}
```

A `ComposedFunctor` overrides the `map` method using `F.map` and `G.lift`: the latter is defined in the `Functor` trait to
map, or to _lift_, a function `f: A => B` to a function `G[A] => G[B]`.

```Scala
trait Functor[F[_]] ... {
  def lift[A, B](f: A => B): F[A] => F[B] = map(_)(f)
}
```

Because `fga` is `F[C]` - where `C = G[A]` -, we need a _function_ from `C` to `D` - where `D = G[B]` - in order to use
`F.map`. But this function is precisely `G.lift(f)`.

2. `ComposedApply`:

```Scala
package cats

private[cats] trait ComposedApply[F[_], G[_]]
    extends Apply[λ[α => F[G[α]]]]
    with ComposedFunctor[F, G] {

  def F: Apply[F]
  def G: Apply[G]

  override def ap[A, B](fgf: F[G[A => B]])(fga: F[G[A]]): F[G[B]] =
    F.ap(F.map(fgf)(G.ap))(fga)

  override def product[A, B](fga: F[G[A]], fgb: F[G[B]]): F[G[(A, B)]] =
    F.map2(fga, fgb)(G.product)
}
```

A `ComposedApply` overrides two methods, `ap` and `product`, at which we look closer:

- in the definition for `ap`, `F.map(fgf)(G.ap): F[G[A] => G[B]]` is used to map `fgf: F[G[A => B]]` through the function
  `G.ap`: the latter, when passed an argument `G[A => B]` yields a partially applied function of type `G[A] => G[B]`, which
  is wrapped by `F.map` in `F`; then, `F.ap` can be applied to it and `fga: F[G[A]]`, result of type `F[G[B]]`;

- in the definition for `product`, `G.product` is a binary function of type `(G[A], G[B]) => G[(A, B)]`: this is the third
  argument to `F.map2`, applied to `fga` and `fgb`, which wraps `G[(A, B)]` in `F`, resulting in the type `F[G[(A, B)]]`.

3. [`ComposedApplicative`](http://typelevel.org/cats/typeclasses/applicative.html#applicatives-compose):

```Scala
package cats

private[cats] trait ComposedApplicative[F[_], G[_]]
    extends Applicative[λ[α => F[G[α]]]]
    with ComposedApply[F, G] {

  def F: Applicative[F]
  def G: Applicative[G]

  override def pure[A](x: A): F[G[A]] = F.pure(G.pure(x))
}
```

A `ComposedApplicative` overrides just one method, `pure`: argument `x` is lifted in `G`, which then is lifted in `F`.

4. `ComposedFoldable`:

```Scala
package cats

private[cats] trait ComposedFoldable[F[_], G[_]] extends Foldable[λ[α => F[G[α]]]] {
  def F: Foldable[F]
  def G: Foldable[G]

  override def foldLeft[A, B](fga: F[G[A]], b: B)(f: (B, A) => B): B =
    F.foldLeft(fga, b)((b, ga) => G.foldLeft(ga, b)(f))

  override def foldRight[A, B](fga: F[G[A]], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
    F.foldRight(fga, lb)(G.foldRight(_, _)(f))

  override def toList[A](fga: F[G[A]]): List[A] =
    F.toList(fga).flatMap(G.toList)

  override def toIterable[A](fga: F[G[A]]): Iterable[A] =
    F.toIterable(fga).flatMap(G.toIterable)
}
```

A `ComposedFoldable` overrides four methods:

- `foldLeft` - function `f` is used inside the inner `G.foldLeft`, while the folding function for the outer `F.foldLeft`
  passes the two arguments - an accumulator `b: B` and a `ga: G[A]` - to `G.foldLeft`;

- `foldRight` - same as `foldLeft`, only the folding function for the outer `F.foldRight` is anonymous;

- `toList` - while `F.toList(fga)` creates a list of type `List[G[A]]`, the latter uses `flatMap` to flatten the mapped lists
  `G.toList(_: G[A]): List[A]`;

- `toIterable` - same as `toList`, only for `Iterable`.

5. `ComposedTraverse`:

```Scala
package cats

private[cats] trait ComposedTraverse[F[_], G[_]]
    extends Traverse[λ[α => F[G[α]]]]
    with ComposedFoldable[F, G]
    with ComposedFunctor[F, G] {
  def F: Traverse[F]
  def G: Traverse[G]

  override def traverse[H[_]: Applicative, A, B](fga: F[G[A]])(f: A => H[B]): H[F[G[B]]] =
    F.traverse(fga)(G.traverse(_)(f))

  override def mapAccumulate[S, A, B](init: S, fga: F[G[A]])(f: (S, A) => (S, B)): (S, F[G[B]]) =
    F.mapAccumulate(init, fga)(G.mapAccumulate(_, _)(f))
}
```

A `ComposedTraverse` overrides two methods:

- `traverse` - with an `H[_]: Applicative`, function `f` is used by the inner `G.traverse` with anonymous parameter of type
  `G[A]` and result type `H[G[B]]`, while the outer `F.traverse` - using the same `H[_]` - traverses a `fga: F[G[A]]` via a
  function `G[A] => H[G[B]]` to an `H[F[G[B]]]`;

- `mapAccumulate` - same as `traverse`, but with binary functions; `G.mapAccumulate` yields a result of type `(S, G[B])`, so
  the third argument to `F.mapAccumulate` is an anonymous function `(S, G[A]) => (S, G[B])`.

Composing Failure
-----------------

A problem with composing typeclasses in this way is their scarceness: only a few typeclasses can compose.

For example, trying to compose two `FlatMap`s:

```Scala
private[cats] trait ComposedFlatMap[F[_], G[_]] extends FlatMap[λ[α => F[G[α]]]] {
  def F: FlatMap[F]
  def G: FlatMap[G]

  override def flatten[A](ffa: F[G[F[G[A]]]]): F[G[A]] = ???

  private def flattenʹ(ffgga: F[F[G[G[A]]]]): F[G[A]] = F.map(F.flatten(ffgga))(G.flatten)
}
```

it is impossible - in the general case - to pass from `F[G[F[G[A]]]]` to `F[G[A]]` (perhaps a `flattenʹ` instead, but this is
totally different than `flatten`).

We could not do better for `CoflatMap` either:

```Scala
private[cats] trait ComposedCoflatMap[F[_], G[_]] extends CoflatMap[λ[α => F[G[α]]]] {
  def F: CoflatMap[F]
  def G: CoflatMap[G]

  override def coflatten[A](fa: F[G[A]]): F[G[F[G[A]]]] = ???

  private def coflattenʹ(fa: F[G[A]]): F[F[G[G[A]]]] = F.coflatten(F.map(fa)(G.coflatten))
}
```

(perhaps a `coflattenʹ` instead, but this is totally different than `coflatten`).

Composing examples
------------------

An example of composing `List` with `Option` is the following:

```scala
scala> Monad[List].compose[Option]
val res0: cats.Applicative[[α] =>> List[Option[α]]] = cats.Alternative$$anon$1@632bf437
```

`Monad`s cannot compose - as `FlatMap`s cannot compose -, so `res0` is not a `Monad`, but a most specific typeclass - like
`Applicative`.

Now we can use the `map` or `pure` methods on a _unique_ typeclass instance (`res0`):

```scala
scala> res0.pure(0)
val res1: List[Option[Int]] = List(Some(0))

scala> res0.map(res1)(_ + 1)
val res2: List[Option[Int]] = List(Some(1))
```

Of course, _distinct_ typeclass instances can be used with proper distinct methods:

```scala
scala> Functor[List].compose[Option].map(res1)(_ + 1)
val res3: List[Option[Int]] = List(Some(1))

scala> Apply[List].compose[Option].ap(List(Some((_: Int) + 1), None))(res1)
val res4: List[Option[Int]] = List(Some(1), None)
```

Composing Monad Transformers
----------------------------

Monad transformers are _already composing_ a varying context (`F[_]`) with a fixed part (`Option`, `Either`, `Tuple2`, etc).
And, they coerce `F` to abide by a certain typeclass instance, _only_ per specific method. It is the developers who must
adhere to a method's _contract_ - and know what typeclass is required for using the method -, that brings order to chaos, and
not the other way around: developers having to adapt continuously to _nuances_ in the uses of the method.

`EitherT`, for example, has two "fold" methods, one prompting for a `Functor`, the other for a `FlatMap`:

```Scala
  def fold[C](fa: A => C, fb: B => C)(implicit F: Functor[F]): F[C] = ???
  def foldF[C](fa: A => F[C], fb: B => F[C])(implicit F: FlatMap[F]): F[C] = ???
```

Monad transformers are `case class`es carrying value(s) wrapped in an `F[_]`. Once this `case class` is instantiated, user
code may apply methods directly on the instance, rather than its (carried or) wrapped value(s). They could actually be
(named) like the traits: `ComposedEither[F[_]]`, `ComposedOption[F[_]]`, etc, but where `F` _cannot_ be abstracted to a
unique typeclass instance member, if not an `implicit` parameter per method.

[Previous](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-2-EitherT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md)
