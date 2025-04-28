[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-5-kleisli/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

`StateT`
--------

`StateT` is actually a type alias for `IndexedStateT`:

```
package cats

type StateT[F[_], S, A] = IndexedStateT[F, S, S, A]
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

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-5-kleisli/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md)
