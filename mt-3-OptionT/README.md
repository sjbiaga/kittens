[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-2-EitherT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

`OptionT`
---------

Methods à la `map` or `flatMap`
-------------------------------

`transform`, `flatTransform`

`map`, `imap`, `contramap`, `semiflatMap`, `mapFilter`, `flatMap`, `flatMapF`, `subflatMap`

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

Companion Object
----------------

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-2-EitherT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md)
