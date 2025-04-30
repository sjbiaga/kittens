[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-3-OptionT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-5-ReaderT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

`IorT`
---------

Methods à la `map` or `flatMap`
-------------------------------

### Methods based on `transform`

`map`, `bimap`, `leftMap`, `leftFlatMap`, `leftSemiflatMap`

### Methods based on `flatTransform`

Unlike for [`EitherT`](https://github.com/sjbiaga/kittens/blob/main/mt-2-EitherT/README.md#methods-based-on-flattransform),
there is no `biflatMap`, nor can one be defined, even if a definition could be reached:

```Scala
def biflatMap[C, D](fa: A => IorT[F, C, D], fb: B => IorT[F, C, D])(implicit F: Monad[F], C: Semigroup[C], D: Semigroup[D]): IorT[F, C, D] =
  flatTransform(_.fold(fa(_).value, fb(_).value,
    {
      (a, b) =>
        F.map2(fa(a).value, fb(b).value) {
          case (Ior.Left(c1), Ior.Left(c2)) => Ior.Left(C.combine(c1, c2))
          case (Ior.Right(d1), Ior.Right(d2)) => Ior.Right(D.combine(d1, d2))
          case (Ior.Both(c1, d1), Ior.Both(c2, d2)) => Ior.Both(C.combine(c1, c2), D.combine(d1, d2))
          case _ => ???
        }
    }
  ))
```

because `Ior#fold` takes _three_ function parameters, the _third_ binary function being impossible to implement in terms of
`fa` and `fb`, due to the missing cases - `C` and `D` cannot be combined -, so it cannot be completed.

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

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-3-OptionT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-5-ReaderT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)
