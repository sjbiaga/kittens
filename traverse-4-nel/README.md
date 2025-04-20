[First](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/traverse-3-lazylist/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/traverse-5-set-expr/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md)

Lesson 07: Traversable (cont'd)
===============================

`Traverse[NonEmptyList]`
------------------------

Sometimes a collection can be reduced to another collection - such is the case for `NonEmptyList` -, and the former delegates
to the latter the `traverse`al using _the same_ function `f` - because the two collections have the same base type:

```Scala
final case class NonEmptyList[+A](head: A, tail: List[A]) extends ... {
  def traverse[G[_], B](f: A => G[B])(implicit G: Applicative[G]): G[NonEmptyList[B]] =
    G.map2Eval(f(head), Always(Traverse[List].traverse(tail)(f)))(NonEmptyList(_, _)).value
}
```

This is a unique example where `map2Eval` is used in non-empty _initialization_.

Note that, had we used `G.map2` instead of `G.map2Eval`:

```Scala
G.map2(f(head), Traverse[List].traverse(tail)(f))(NonEmptyList(_, _))
```

and `G: Applicative[G]` had a fail fast semantics, failing on `head` would not have short circuited the traversal on `tail`.

The reader is urged to visit the implementation of other typeclass instances of the `Traverse` typeclass, like for the
optional types `scala.Option`, `cats.data.Validated`, and `cats.data.IoR`, `Vector` or `MapK[K, _]`.

[First](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/traverse-3-lazylist/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/traverse-5-set-expr/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md)
