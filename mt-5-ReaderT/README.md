[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-6-WriterT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

`ReaderT`
---------

`ReaderT` is actually a type alias for `Kleisli`:

```
package cats

type ReaderT[F[_], -A, B] = Kleisli[F, A, B]
```

Methods à la `map` or `flatMap`
-------------------------------

Methods related to errors
-------------------------

Traversing or folding methods
-----------------------------

`to*` methods
-------------

Other methods
-------------

Methods from the companion object
---------------------------------

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-6-WriterT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md)
