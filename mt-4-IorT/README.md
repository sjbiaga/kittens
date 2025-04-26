[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-3-OptionT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-5-ReaderT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

`IorT`
---------

Methods à la `map` or `flatMap`
-------------------------------

####Methods based on `transform`

`map`, `bimap`, `leftMap`, `leftFlatMap`, `leftSemiflatMap`

####Methods based on `flatTransform`

`flatMap`, `subflatMap`, `semiflatMap`

Methods corresponding to `Ior`
---------------------------------

`fold`, `foldF`, `isLeft`, `isRight`, `isBoth`, `getOrElse`, `getOrElseF`, `getOrRaise`, `valueOr`

```Scala
def fold[C](fa: A => C, fb: B => C, fab: (A, B) => C)(implicit F: Functor[F]): F[C] =
  F.map(value)(_.fold(fa, fb, fab))
def foldF[C](fa: A => F[C], fb: B => F[C], fab: (A, B) => F[C])(implicit F: FlatMap[F]): F[C] =
  F.flatMap(value)(_.fold(fa, fb, fab))
```

`forall`, `exists`, `merge`

Methods related to errors
-------------------------

Traversing or folding methods
-----------------------------

`traverse`, `foldLeft`, `foldRight`

`to*` methods
-------------

`toOption`, `toEither`, `toValidated`

Other methods
-------------

`applyAlt`, `mapk`

Methods from the companion object
---------------------------------

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-3-OptionT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-5-ReaderT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md)
