[Previous](https://github.com/sjbiaga/kittens/blob/main/expr-02-eval/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-04-parser/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/expr-09-ring/README.md)

Lesson 03: A Rich Language of Expressions (cont'd)
==================================================

`Expr` as [`Functor`](https://typelevel.org/cats/typeclasses/functor.html)
--------------------------------------------------------------------------

`Cats` is a library centered around `Functor`s. A functor is a type of higher-kind `* -> *`, or, with a hole. In the Category
Theory branch of `Mathematics` (hence the name "Cats"), functors have a source and a target category,

* mapping compositions of functions from the source category to the composition of the mappings in the target category, and
* identities to identities.

In Scala, `Option`, `List` or `Future` are examples of functors. `Expr` as well is a functor, but in order to be so too in
`Cats`, a [_typeclass instance_](https://scalawithcats.com/dist/scala-with-cats-1.html#type-class-instances) of the
higher-kinded (`(* -> *) -> *`) `Functor` [typeclass](https://scalawithcats.com/dist/scala-with-cats-1.html#the-type-class)
must be given for `Functor[Expr]`.

What is `Functor`? It is a Scala _trait_ with one defined method named `map`. It does exactly what it says: it represents a
trait of some higher-kinded types of kind `* -> *`, namely to have the ability to _map_ a function `f: A => B` in the domain
(source) of the functor `F[_]` to a function `F[A] => F[B]` in its codomain (target). Of course, `A` can very well be some
`F[X]`, which means that the codomain is included in the domain. In any case, what really matters is that `Functor` is a sort
of an identification for functors, whichever functor `F[_]` is given a typeclass instance for `Functor[F]` identifying itself
as such.

It is also the most simple and the very first encountered - by developers - concept of Category Theory in `Cats`, albeit it
actually inherits another - more basic - trait, the `Invariant` trait.

Here follows the typeclass for `Functor[Expr]`; except `Val`, the other `enum` `case` classes map to themselves as operators,
but with possibly distinct, mapped, operands. `Val` is the only `enum` `case` class that really applies the argument function
`f: A => B`:

```Scala
import cats.Functor
implicit val kittensExprFunctor: Functor[Expr] =
  new Functor[Expr]:
    def map[A, B](xa: Expr[A])(f: A => B): Expr[B] =
      xa match
        case Val(a)        => Val(f(a))
        case Inv(rhs)      => Inv(map(rhs)(f))
        case Add(lhs, rhs) => Add(map(lhs)(f), map(rhs)(f))
        case Sub(lhs, rhs) => Sub(map(lhs)(f), map(rhs)(f))
        case Mul(lhs, rhs) => Mul(map(lhs)(f), map(rhs)(f))
        case Div(lhs, rhs) => Div(map(lhs)(f), map(rhs)(f))
        case it @ ( Zero | One ) => it
```

In order to _use_ the `map` method, the `functor` syntax must be in scope. `Cats` employs a sophisticated system of implicits
to this end. This mechanism is explained in [Lesson 05 - Resolving `Monoid`s](https://github.com/sjbiaga/kittens/blob/main/monoid-4-resolve/README.md#resolving-monoids). Thus:

```scala
scala> import cats.syntax.functor._
scala> (Inv(Val(2)): Expr[Int]).map(_ / 2)
val res0: Expr[Int] = Inv(Val(1))
```

Natural Transformations: Swapping the Additive with the Multiplicative
----------------------------------------------------------------------

Category Theory is quite abstract, and the more advanced notions are introduced, the more difficult they get. Natural
transformations are known as morphisms of functors. In `Cats`, they are available in the package `cats.arrow`, as the
higher-kinded `FunctionK` trait of kind `(* -> *, * -> *) -> *`, also written `~>`. Given two functors `F[_]` and `G[_]`, it
defines a `SAM` method `apply[A](fa: F[A]): G[A]`.

Nevertheless, a very straightforward "function" or natural transformation of signature `Expr ~> Expr` is that of swapping the
additive and the multiplicative parts with one another: by pattern-matching on the parameter `expr: Expr[T]`, we can swap
operators `Zero` with `One`, `Add` with `Mul`, and `Sub` with `Div` - and vice-versa. The operands are swapped in a recursive
manner. The implementation is also very intuitive - much like [`eval`](https://github.com/sjbiaga/kittens/blob/main/expr-02-eval/README.md#evaluation-of-expressions).

```Scala
import cats.~>
val swap: Expr ~> Expr =
  new (Expr ~> Expr):
    def apply[T](expr: Expr[T]): Expr[T] =
      expr match
        case Zero          => One
        case One           => Zero
        case Add(lhs, rhs) => Mul(apply(lhs), apply(rhs))
        case Sub(lhs, rhs) => Div(apply(lhs), apply(rhs))
        case Mul(lhs, rhs) => Add(apply(lhs), apply(rhs))
        case Div(lhs, rhs) => Sub(apply(lhs), apply(rhs))
        case Inv(lhs)      => Inv(apply(lhs))
        case it            => it
```

Note that applying `swap` _twice_ is the identity natural transformation.

Since swapping can be performed otherwise without the appearance of a natural transformation, it raises the question as to
why use a natural transformation. Many `trait`s in `Cats` have a `mapK` method with a natural transformation as parameter.
For instance, the `cats.free.Free` monad allows to change its suspension functor via a natural transformation - so let us do
it trivially:

```Scala
import cats.free.Trampoline, cats.arrow.FunctionK

Trampoline.delay(()).mapK(FunctionK.id)
```

We will come back to this topic in [Lesson 06](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md).

[Previous](https://github.com/sjbiaga/kittens/blob/main/expr-02-eval/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-04-parser/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/expr-09-ring/README.md)
