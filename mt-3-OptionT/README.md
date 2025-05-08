[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-2-EitherT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

`OptionT`
---------

Unlike for [`EitherT`](https://github.com/sjbiaga/kittens/blob/main/mt-2-EitherT/README.md#methods-based-on-flattransform) or
for [`IorT`](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md#methods-based-on-flattransform), there are no
methods whose names are prefixed with `bi*` or contain `*left*`.

Methods à la `map` or `flatMap`
-------------------------------

The majority of these methods resort to other two, `transform` and `flatTransform` methods:

```Scala
def transform[B](f: Option[A] => Option[B])(implicit F: Functor[F]): OptionT[F, B] =
  OptionT(F.map(value)(f))

def flatTransform[B](f: Option[A] => F[Option[B]])(implicit F: FlatMap[F]): OptionT[F, B] =
  OptionT(F.flatMap(value)(f))
```

Both return an `OptionT[F, B]`. The (slight) difference between the two is that:

- the latter's parameter is a function resulting lifted to an `F[Option[B]]`, whereas the former returns a bare `Option[B]`;

- `F` must be a typeclass instance of either the `Functor`, or, respectively, the `FlatMap` typeclass, for `F[_]`.

The implementations too are very simple - given the type of the parameter function `f`. Both wrap the result in an `OptionT`
from application of -, and pass the same two parameters `value` and `f` to - either `F.map`, or, respectively, `F.flatMap`.

### Methods based on `transform`

1. One of the two methods required to turn `OptionT` into a monad is `map`:

```Scala
def map[B](f: A => B)(implicit F: Functor[F]): OptionT[F, B] =
  transform(_.map(f))
```

having a function parameter of a type appropriate to invoke the (corresponding) method `map` on an (anonymous) `Option[A]`
receiver.

2. An interesting method `subflatMap`:

```Scala
def subflatMap[B](f: A => Option[B])(implicit F: Functor[F]): OptionT[F, B] =
  transform(_.flatMap(f))
```

has a function parameter of a type appropriate to invoke the (corresponding) method `flatMap` on an (anonymous) `Option[A]`
receiver.

3. `mapFilter` (generally) takes a function parameter `A => Option[B]`, which - in the case of `OptionT` alone -
   coincidentally matches exactly the signature of - and so it is an alias for - `subflatMap`.

3. Because `Option` is an `IterableOnce`, it can `filter` and `filterNot` (`withFilter` - a non-necessary but allowed method
   to turn `OptionT` into a Scala monad - is an alias to `filter`), so `OptionT` can too - in the inner `Option[_]` context:

```Scala
def filter(p: A => Boolean)(implicit F: Functor[F]): OptionT[F, A] =
  transform(_.filter(p))
def filterNot(p: A => Boolean)(implicit F: Functor[F]): OptionT[F, A] =
  transform(_.filterNot(p))
```

5. For the same reason as in (4), `OptionT` can `collect` in the inner `Option[_]` context:

```Scala
def collect[B](f: PartialFunction[A, B])(implicit F: Functor[F]): OptionT[F, B] =
  transform(_.collect(f))
```

### Methods based on `flatTransform`

1. `flatMap` is a quasi-alias to `flatMapF`:

```Scala
def flatMap[B](f: A => OptionT[F, B])(implicit F: Monad[F]): OptionT[F, B] =
  flatMapF(f(_).value)

def flatMapF[B](f: A => F[Option[B]])(implicit F: Monad[F]): OptionT[F, B] =
  flatTransform(_.fold(F.none[B])(f))
```

The `Monad[F]` typeclass instance is required because `flatTransform` asks for a `FlatMap[F]` typeclass instance, whereas
`Monad` inherits `Applicative#none`; we can make the following type ascriptions about the anonymous function (inside
`flatTransform`), knowing `f: A => F[Option[B]]`:

```Scala
(_: Option[A]).fold(F.none[B]: F[Option[B]])(f): F[Option[B]]
```

which tells us that its type is `Option[A] => F[Option[B]]`.

2. We have seen a `filter` method based on `transform` that corresponds to `Option#filter`. The `filterF` method has as type
   parameter a function resulting in a `Boolean` lifted to an `F[_]` context:

```Scala
def filterF(p: A => F[Boolean])(implicit F: Monad[F]): OptionT[F, A] =
  flatTransform(_.fold(F.none)(a => F.map(p(a))(if (_) Some(a) else None)))
```

For an instance of `Some(a: A)`, the `Option#filter` method returns `None` if the `Boolean` predicate is `false` of `a`. We
cannot "test" the predicate, because it is not a `Boolean`; only in the second parameter to `F.map(p(a))` do we have access
to the value of the predicate, but for this we need an `a: A`. So, we fold an `Option[A]` receiver which `flatTransform`
provides in the second parameter to `F.flatMap(value)`, and return `None` if the `Boolean` value of the predicate is `false`.
Otherwise, we re-instantiate `Some(a)`; the original implementation of `filterF` - without `fold` and new instance - is more
efficient:

```Scala
def filterF(p: A => F[Boolean])(implicit F: Monad[F]): OptionT[F, A] =
  OptionT(F.flatMap(value) {
    case v @ Some(a) => F.map(p(a)) { if (_) v else None }
    case _           => F.none
  })
```

3. Unlike `flatMap` or `subflatMap`, the `semiflatMap` method has a parameter function resulting in only a lifted `F[B]`:

```Scala
def semiflatMap[B](f: A => F[B])(implicit F: Monad[F]): OptionT[F, B] =
  flatMap(f andThen OptionT.liftF)
```

and its implementation resorts to `flatMap`, by first composing `f` with the `OptionT.liftF` method value.

4. Among the "tap" methods, `semiflatTap` delegates to `semiflatMap`: 

```Scala
def semiflatTap[B](f: A => F[B])(implicit F: Monad[F]): OptionT[F, A] =
  semiflatMap(F.tapF(f))
```

whereas `flatTapNone` most resembles `flatMapF` (1) or `filterF` (2), except that it invokes `FlatMap#flatTap` instead of
`FlatMap#flatMap`:

```Scala
def flatTapNone[B](ifNone: => F[B])(implicit F: Monad[F]): OptionT[F, A] =
  OptionT(F.flatTap(value)(_.fold(F.void(ifNone))(_ => F.unit)))
```

such that, making the following type ascriptions:

```Scala
F.flatTap(value: F[Option[A]])((_: Option[A]).fold(F.void(ifNone): F[Unit])((_: A) => F.unit): Option[F[Unit]]))
```

the first parameter to `F.flatTap` has type `F[Option[A]]`, while the second anonymous function parameter has type
`Option[A] => Option[F[Unit]]`, resulting in the (same) type `F[Option[A]`. Note that `F.void(ifNone)` maps the type `F[B]`
(of `ifNone`) `as` the type `F[Unit]`.

Methods corresponding to `Option`
---------------------------------

The first group of methods is made of: `fold`/`cata`, `foldF`/`cataF`, `foreachF`, `getOrElse`, `getOrElseF`, and
`getOrRaise`. These methods' return types are lifted strictly into `F[_]`.

The methods ending in `F` use a `FlatMap[F]` typeclass instance, the others use a `Functor[F]` typeclass instance;
`foreachF` and `getOrElseF` use a `Monad[F]` typeclass instance, while `getOrRaise` uses a `MonadError[F]` typeclass instance.

`cata` and `cataF` are aliases to `fold`/`foldF` - the difference being that in the signature, the (first) two parameters are
separated by comma, rather than in separate parameter lists.

1. The `Option#fold` method allows to avoid boilerplate pattern matching code; its parameters are the same as the `OptionT`
   two methods':

```Scala
def fold[B](default: => B)(f: A => B)(implicit F: Functor[F]): F[B] =
  F.map(value)(_.fold(default)(f))
def foldF[B](default: => F[B])(f: A => F[B])(implicit F: FlatMap[F]): F[B] =
  F.flatMap(value)(_.fold(default)(f))
```

2. `foreachF` is a quasi-alias to `foldF`, its function parameter of type `A => F[Unit]` is just used for effect:

```Scala
def foreachF(f: A => F[Unit])(implicit F: Monad[F]): F[Unit] =
  foldF(F.unit)(f)
```

4. The `getOrElse` and `getOrElseF` methods resort to, respectively, `fold` and `foldF`:

```Scala
def getOrElse[B >: A](default: => B)(implicit F: Functor[F]): F[B] =
  fold(default)(identity)
def getOrElseF[B >: A](default: => F[B])(implicit F: Monad[F]): F[B] =
  foldF(default)(F.pure)
```

5. [`getOrRaise`](#methods-related-to-errors) is a quasi-alias for `getOrElseF`.

The second group of methods is made of `forall`, `exists`, `isDefined`, `isEmpty`, `orElse`, and `orElseF`, which correspond
to the same `Option` methods:

```Scala
def exists(f: A => Boolean)(implicit F: Functor[F]): F[Boolean] =
  F.map(value)(_.exists(f))
def forall(f: A => Boolean)(implicit F: Functor[F]): F[Boolean] =
  F.map(value)(_.forall(f))
def isDefined(implicit F: Functor[F]): F[Boolean] =
  F.map(value)(_.isDefined)
def isEmpty(implicit F: Functor[F]): F[Boolean] =
  F.map(value)(_.isEmpty)
```

The above methods all use a `Functor[F]` typeclass instance, resorting to the `Functor#map` method. However, `orElseF` uses
an `Apply[F]` typeclass instance, resorting to the `Apply#map2` method:

```Scala
def orElse(default: OptionT[F, A])(implicit F: Apply[F]): OptionT[F, A] =
  orElseF(default.value)
def orElseF(default: F[Option[A]])(implicit F: Apply[F]): OptionT[F, A] =
  OptionT(F.map2(value, default)(_.orElse(_)))
```

Methods related to errors
-------------------------

The only method is `getOrRaise`, which aliases `getOrElseF`, passing it the error `e: E` lifted into `MonadError[F, E]`:

```Scala
def getOrRaise[E](e: => E)(implicit F: MonadError[F, E]): F[A] =
  getOrElseF(F.raiseError(e))
```

Traversing or folding methods
-----------------------------

`traverse`, `mapAccumulate`, `foldLeft`, `foldRight`

`to*` methods
-------------

`toRight`, `toRightF`, `toLeft`, `toLeftF`, `toNested`

Other methods
-------------

The `imap` and `contramap` methods are possible given, respectively, an `Invariant[F]` and a `Contravariant[F]` typeclass
instance, because for a _receiver_ of type `Option[A]` and function `f: A => B`, the following type can be ascribed to the
anonymous function `_.map(f): Option[A] => Option[B]`; such a function can be passed as second (or third) argument to,
respectively, `F.imap` and `F.contramap`:

```Scala
def imap[B](f: A => B)(g: B => A)(implicit F: Invariant[F]): OptionT[F, B] =
  OptionT {
    F.imap(value)(_.map(f))(_.map(g))
  }
def contramap[B](f: B => A)(implicit F: Contravariant[F]): OptionT[F, B] =
  OptionT {
    F.contramap(value)(_.map(f))
  }
```

where the following type ascriptions can be made:

```Scala
F.imap(value: F[Option[A]]): (Option[A] => Option[B]) => (Option[B] => Option[A]) => F[Option[B]]
F.contramap(value: F[Option[A]]): (Option[B] => Option[A]) => F[Option[B]]
```

`compare`, `partialCompare`, `===`, `mapK`

Methods from the companion object
---------------------------------

`pure` - and its alias `some` - is not defined as a method in the usual sense, but through a technique called
[partially applied type params](http://typelevel.org/cats/guidelines.html#partially-applied-type-params), which requires two
steps (and two methods) in order to help with the type inference of the `OptionT` type parameters `F[_]` and `A`; when all
type parameters and parameters are known, `pure` is equivalent with:

```Scala
OptionT(F.pure(Some(value: A)))
```

In a similar way, `none` just lifts `None` into an `Applicative` `F[_]` and wraps it in an `OptionT`:

```Scala
def none[F[_], A](implicit F: Applicative[F]): OptionT[F, A] =
  OptionT(F.none)
```

The `fromOption` method is like `OptionT.pure` or `OptionT.none`, but the argument is already lifted into `Option`.

The `liftF` method lifts into the "composed" context `F[Option[_]]` the unwrapped value of its parameter `fa: F[A]`:

```Scala
def liftF[F[_], A](fa: F[A])(implicit F: Functor[F]): OptionT[F, A] =
  OptionT(F.map(fa)(Some(_)))
```

The lifting in the inner `Option[_]` context is just instantiating a `Some` object, whereas the unwrapping/wrapping from/into
`F` - by the `Functor[F]` typeclass instance - might be more intricate.

The `when`/`unless` pair of methods delegate to `some(a: A)` and `none`, depending whether a `cond`ition is `true`/`false`;
`unless` is a quasi-alias for `when` with the `cond`ition negated:

```Scala
def when[F[_], A](cond: Boolean)(a: => A)(implicit F: Applicative[F]): OptionT[F, A] =
  if (cond) OptionT.some[F](a) else OptionT.none[F, A]
def unless[F[_], A](cond: Boolean)(a: => A)(implicit F: Applicative[F]): OptionT[F, A] =
  OptionT.when(!cond)(a)
```

The `whenF`/`unlessF` pair of methods delegate to `liftF(fa: F[A]` and `none`, depending whether a `Boolean` `cond`ition is
`true`/`false`; `unlessF` is a quasi-alias for `whenF` with the `cond`ition negated:

```Scala
def whenF[F[_], A](cond: Boolean)(fa: => F[A])(implicit F: Applicative[F]): OptionT[F, A] =
  if (cond) OptionT.liftF(fa) else OptionT.none[F, A]
def unlessF[F[_], A](cond: Boolean)(fa: => F[A])(implicit F: Applicative[F]): OptionT[F, A] =
  OptionT.whenF(!cond)(fa)
```

The _m_onadic version `whenM`/`unlessM` methods lift into `F[Option[_]]` the same as `liftF` and `none`:

```Scala
def whenM[F[_], A](cond: F[Boolean])(fa: => F[A])(implicit F: Monad[F]): OptionT[F, A] = OptionT(
  F.ifM(cond)(ifTrue = F.map(fa)(Some(_)), ifFalse = F.none)
)
def unlessM[F[_], A](cond: F[Boolean])(fa: => F[A])(implicit F: Monad[F]): OptionT[F, A] = OptionT(
  F.ifM(cond)(ifTrue = F.none, ifFalse = F.lift(Option(_))(fa))
)
```

but use the `ifM` method defined in the `FlatMap` trait inherited by `Monad`:

```Scala
trait FlatMap[F[_]] ... {
  def ifM[B](fa: F[Boolean])(ifTrue: => F[B], ifFalse: => F[B]): F[B] =
    flatMap(fa)(if (_) ifTrue else ifFalse)
}
```

because the condition `cond: F[Boolean]` is lifted into the `F[_]` context.

`liftK`, `whenK`, `unlessK`

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-2-EitherT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)
