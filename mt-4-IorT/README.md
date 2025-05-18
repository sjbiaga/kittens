[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-3-OptionT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-5-ReaderT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

[`IorT`](https://typelevel.org/cats/datatypes/iort.html)
--------------------------------------------------------

Methods à la `map` or `flatMap`
-------------------------------

The majority of these methods resort to other two, `transform` and `flatTransform` methods:

```Scala
def transform[C, D](f: Ior[A, B] => Ior[C, D])(implicit F: Functor[F]): IorT[F, C, D] =
  IorT(F.map(value)(f))

def flatTransform[C, D](f: Ior[A, B] => F[Ior[C, D]])(implicit F: FlatMap[F]): IorT[F, C, D] =
  IorT(F.flatMap(value)(f))
```

### Methods based on `transform`

`map`, `bimap`, `leftMap`, `subflatMap`, `swap`

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

`flatMap`, `flatMapF`, `semiflatMap`, `leftFlatMap`, `leftSemiflatMap`

`semiflatTap`

Methods corresponding to `Ior`
---------------------------------

`fold`, `foldF`, `isLeft`, `isRight`, `isBoth`, `getOrElse`, `getOrElseF`, `getOrRaise`, `merge`, `valueOr`

```Scala
def fold[C](fa: A => C, fb: B => C, fab: (A, B) => C)(implicit F: Functor[F]): F[C] =
  F.map(value)(_.fold(fa, fb, fab))
def foldF[C](fa: A => F[C], fb: B => F[C], fab: (A, B) => F[C])(implicit F: FlatMap[F]): F[C] =
  F.flatMap(value)(_.fold(fa, fb, fab))
```

`forall`, `exists`

Methods related to errors
-------------------------

`getOrRaise`

Traversing and folding methods
------------------------------

`traverse`, `foldLeft`, `foldRight`

`to*` methods
-------------

`toOption`, `toEither`, `toValidated`

Other methods
-------------

`applyAlt`, `mapK`, `===`, `compare`, `combine`

Methods from the companion object
---------------------------------

Typeclass instances
-------------------

A typeclass instance of the [`Defer`](https://github.com/sjbiaga/kittens/blob/main/recursion-4-Defer/README.md) typeclass
asks for an `implicit` `F; Defer[F]` typeclass instance in scope. Given the `fa: => IorT[F, E, A]` parameter, the method
`defer` is invoked with receiver `F` and argument `fa.value`. This argument uses `fa` which is a call-by-name parameter, but
the `defer` method is also passed a call-by-name argument, so `fa.value` will not be evaluated: the call-by-name flavor of
the `fa` parameter continues in the argument `fa.value`:

```Scala
implicit def ... (implicit F: Defer[F]): ... =
  new Defer[IorT[F, E, *]] {
	def defer[A](fa: => IorT[F, E, A]): IorT[F, E, A] =
	  IorT(F.defer(fa.value))
  }
```

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-3-OptionT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-5-ReaderT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)
