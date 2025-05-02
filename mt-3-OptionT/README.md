[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-2-EitherT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

`OptionT`
---------

Methods à la `map` or `flatMap`
-------------------------------

Unlike for [`EitherT`](https://github.com/sjbiaga/kittens/blob/main/mt-2-EitherT/README.md#methods-based-on-flattransform) or
for [`IorT`](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md#methods-based-on-flattransform), there are no
methods whose names are prefixed with `bi*` or contain `*left*`.

### Methods based on `transform`

`map`,

### Methods based on `flatTransform`

`imap`, `contramap`,
`semiflatMap`, `mapFilter`, `flatMap`, `flatMapF`, `subflatMap`

`mapFilter` (generally) takes a function parameter `A => Option[B]`, which - in the case of `OptionT` alone - coincidentally
matches exactly the signature of - and so it is an alias for - `subflatMap`:

```Scala
def subflatMap[B](f: A => Option[B])(implicit F: Functor[F]): OptionT[F, B] =
  transform(_.flatMap(f))
```

"tap" methods
`semiflatTap`, `flatTapNone`

`collect`

Methods corresponding to `Option`
---------------------------------

The first group
`fold`/`cata`, `foldF`/`cataF`, `foreachF`, `getOrElse`, `getOrElseF`, `getOrRaise`

The methods ending in `F` use a `FlatMap[F]` typeclass instance, the others use a `Functor[F]` typeclass instance;

`getOrElseF` and `valueOrF` use a `Monad[F]` typeclass instance, while `getOrRaise` uses a `MonadError[F]` typeclass instance.

The second group
    `forall`, `exists`, `filter`, `filterF`, `filterNot`, `withFilter`, `isDefined`, `isEmpty`, `orElse`, `orElseF`

```Scala
def orElseF(default: F[Option[A]])(implicit F: Apply[F]): OptionT[F, A] =
  OptionT(F.map2(value, default)(_.orElse(_)))
```

Methods related to errors
-------------------------

`getOrRaise`

Traversing or folding methods
-----------------------------

`traverse`, `mapAccumulate`, `foldLeft`, `foldRight`

`to*` methods
-------------

`toRight`, `toRightF`, `toLeft`, `toLeftF`, `toNested`

Other methods
-------------

`compare`, `partialCompare`, `===`, `mapk`

Methods from the companion object
---------------------------------

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-2-EitherT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)
