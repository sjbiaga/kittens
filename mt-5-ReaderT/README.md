[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-6-WriterT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

[`ReaderT`](https://typelevel.org/cats/nomenclature.html#kleisli-or-readert)
----------------------------------------------------------------------------

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

Typeclass Instances
-------------------

A typeclass instance of the [`Defer`](https://github.com/sjbiaga/kittens/blob/main/recursion-4-Defer/README.md) typeclass
asks for an `implicit` `F; Defer[F]` typeclass instance in scope. Given the `fa: => Kleisli[F, A, B]` parameter, the method
`defer` is invoked with receiver `F` and argument `cacheFa.run(a)`, where `a: A`. This argument uses `cacheFa` which is a
`lazy` `val`ue designed to evaluate the `fa` call-by-name parameter only once. But the `defer` method is also passed a
call-by-name argument, so `cacheFa.run(a)` will not be evaluated: the call-by-name flavor of the `fa` parameter continues in
the argument `cacheFa.run(a)`:

```Scala
implicit def ... (implicit F: Defer[F]): ... =
  new Defer[Kleisli[F, A, *]] {
	def defer[B](fa: => Kleisli[F, A, B]): Kleisli[F, A, B] = {
	  lazy val cacheFa = fa
	  Kleisli[F, A, B] { a =>
		F.defer(cacheFa.run(a))
	  }
	}
  }
```

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-6-WriterT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)
