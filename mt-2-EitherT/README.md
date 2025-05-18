[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-3-OptionT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

[`EitherT`](https://typelevel.org/cats/nomenclature.html#eithert)
-----------------------------------------------------------------

To return to our ([failed](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md#composing-failure)) example of
`flatten`, this time implemented for `EitherT`, flattening an `EitherT[F, A, EitherT[F, A, D]]` is straight using `flatMap`:

```Scala
extension [F[_], A, B](self: EitherT[F, A, B])
  def flatten[D](implicit F: Monad[F], ev: B <:< EitherT[F, A, D]): EitherT[F, A, D] =
    self.flatMap(ev)
```

We could easily implement also a method `flattenʹ` of type `EitherT[F, A, D]` given that `B <:< F[D]`, flattening an
`F[Either[A, F[D]]]`:

```Scala
extension [F[_], A, B](self: EitherT[F, A, B])
  def flattenʹ[D](implicit F: Monad[F], ev: B <:< F[D]): EitherT[F, A, D] =
    val f: A => F[Either[A, D]] = { a => F.pure(Left(a)) }
    val g: B => F[Either[A, D]] = { b => F.map(ev(b))(Right.apply) }
    EitherT(F.flatMap(self.value)(_.fold(f, g)))
```

or alternatively, using function composition with `andThen` (and some necessary type checker hints):

```Scala
extension [F[_], A, B](self: EitherT[F, A, B])
  def flattenʹ[D](implicit F: Monad[F], ev: B <:< F[D]): EitherT[F, A, D] =
    val f: A => F[Either[A, D]] = Left.apply[A, D] andThen F.pure
    val g: B => F[Either[A, D]] = ev andThen F.lift[D, Either[A, D]](Right.apply)
    EitherT(F.flatMap(self.value)(_.fold(f, g)))
```

or, indirectly via `EitherT#semiflatMap` (which invokes `EitherT#flatMapF` which invokes `EitherT#flatTransform`):

```Scala
extension [F[_], A, B](self: EitherT[F, A, B])
  def flattenʹ[D](implicit F: Monad[F], ev: B <:< F[D]): EitherT[F, A, D] =
    self.semiflatMap(ev)
```

We could even simpler implement a method `flattenF` of type `EitherT[F, A, D]` given that `B <:< F[Either[A, D]]`, flattening
an `F[Either[A, F[Either[A, D]]]]`:

```Scala
extension [F[_], A, B](self: EitherT[F, A, B])
  def flattenF[D](implicit F: Monad[F], ev: B <:< F[Either[A, D]]): EitherT[F, A, D] =
    EitherT {
      F.flatMap(self.value) {
        case Left(a)  => F.pure(Left(a))
        case Right(b) => ev(b)
      }
    }
```

Thus, either flattening an `EitherT[F, A, EitherT[F, A, B]]`, or an `F[Either[A, F[B]]]`, or an (indirect)
`F[Either[A, F[Either[A, B]]]]`, the higher-kinded types `Either` and `F` _alternate_:

```scala
scala> import cats.instances.option._

scala> EitherT(Option(Right(EitherT(Option(Right(1)))))).flatten
val res0: cats.data.EitherT[Option, Nothing, Int] = EitherT(Some(Right(1)))

scala> EitherT(Option(Right(Option(1)))).flattenʹ
val res1: cats.data.EitherT[Option, Nothing, Int] = EitherT(Some(Right(1)))

scala> EitherT(Option(Right(Option(Right(1))))).flattenF
val res2: cats.data.EitherT[Option, Nothing, Int] = EitherT(Some(Right(1)))
```

Convenience methods
-------------------

There are two methods defined in the `EitherUtil` pseudo-companion object:

```Scala
object EitherUtil {
  def foldE[A, B, C, D](self: Either[A, B])(f: A => C, g: B => D): Either[C, D] =
    self.fold(f andThen Left.apply, g andThen Right.apply)

  def foldEF[F[_]: Functor, A, B, C, D](self: Either[A, B])(f: A => F[C], g: B => F[D]): F[Either[C, D]] = {
    val F = Functor[F]
    self.fold(f andThen F.lift(Left.apply), g andThen F.lift(Right.apply))
  }
}
```

that return respectively, an `Either[C, D]` and an `F[Either[C, D]]`, both invoking `Either#fold`:

- `foldE`, `fold`ing with compositions with `Left.apply` / `Right.apply`;

- `foldEF`, `fold`ing with [_lifted_](http://typelevel.org/cats/typeclasses/functor.html#a-different-view) compositions with
  `Left.apply` / `Right.apply`; that is why a typeclass instance of the `Functor` typeclass for `F` is required.

Methods à la `map` or `flatMap`
-------------------------------

The majority of these methods resort to other two, `transform` and `flatTransform` methods:

```Scala
def transform[C, D](f: Either[A, B] => Either[C, D])(implicit F: Functor[F]): EitherT[F, C, D] =
  EitherT(F.map(value)(f))

def flatTransform[C, D](f: Either[A, B] => F[Either[C, D]])(implicit F: FlatMap[F]): EitherT[F, C, D] =
  EitherT(F.flatMap(value)(f))
```

Both return an `EitherT[F, C, D]`. The (slight) difference between the two is that:

- the latter's parameter is a function resulting lifted to an `F[Either[C, D]]`, while the former returns a bare `Either[C, D]`;

- `F` must be a typeclass instance of either the `Functor`, or, respectively, the `FlatMap` typeclass, for `F[_]`.

The implementations too are very simple - given the type of the parameter function `f`. Both wrap the result in an `EitherT`
from application of -, and pass the same two parameters `value` and `f` to - either `F.map`, or, respectively, `F.flatMap`.

### Methods based on `transform`

1. A method `bimap`, with the same types of the two function parameters `f: A => C` and `g: B => D` as those of the last two
   parameters of `EitherUtil.foldE`, invokes it with an (anonymous) `Either[A, B]` argument, passed by `transform`:

```Scala
def bimap[C, D](f: A => C, g: B => D)(implicit F: Functor[F]): EitherT[F, C, D] =
  transform(EitherUtil.foldE(_)(f, g))
```

It is used also by the `map` and `leftMap` methods:

```Scala
def map[D](f: B => D)(implicit F: Functor[F]): EitherT[F, A, D] =
  bimap(identity: A => A, f)
```

```Scala
def leftMap[C](f: A => C)(implicit F: Functor[F]): EitherT[F, C, B] =
  bimap(f, identity: B => B)
```

Both `map` and  `leftMap` invoke `bimap` with the same names of parameters, but in a different order (and of different types
in the choice of the type parameters). The former is also one of the two methods required to turn `EitherT` into a monad.

2. An interesting method `subflatMap`:

```Scala
def subflatMap[D](f: B => Either[A, D])(implicit F: Functor[F]): EitherT[F, A, D] =
  transform(_.flatMap(f))
```

has a function parameter of a type appropriate to invoke the (corresponding) method `flatMap` on an (anonymous) `Either[A, B]`
receiver.

3. [swap](#methods-corresponding-to-either) is another method that invokes the corresponding method `swap` on an (anonymous)
   `Either` receiver.

3. [recover](#methods-related-to-errors) and [ensureOr](#methods-related-to-errors) are other two methods that pattern match
   an `Either` passed by `transform`.

### Methods based on `flatTransform`

1. A most used method is `flatMapF`, demanding that there be an `Applicative[F]` (for `F.pure`) and a `FlatMap[F]` (because of
   the invocation of `flatTransform`), which are - in the least - both inherited by `Monad[F]`:

```Scala
def flatMapF[D](f: B => F[Either[A, D]])(implicit F: Monad[F]): EitherT[F, A, D] =
  flatTransform(_.fold(Left.apply[A, D] andThen F.pure, f))
```

The function parameter `f` has a target type wrapped in `F[_]`. The argument to `flatTransform` is an anonymous function
which invokes `fold` on an `Either[A, B]` receiver: a `Left(a: A)` is mapped to `F.pure(Left(a)): F[Either[A, D]]`, whereas a
`Right(b: B)` is mapped through `f` to the same type.

There are two methods - `flatMap`, `semiflatMap` - implemented via `flatMapF`:

```Scala
def flatMap[D](g: B => EitherT[F, A, D])(implicit F: Monad[F]): EitherT[F, A, D] =
  flatMapF(g(_).value)

def semiflatMap[D](g: B => F[D])(implicit F: Monad[F]): EitherT[F, A, D] =
  flatMapF(g andThen F.lift(Right.apply))
```

- Unlike `flatMapF` which maps an `f: B => F[Either[A, D]]`, the `semiflatMap` method maps a `g: B => F[D]`: so with `D` as
target, instead of `Either[A, D]`, lifted in the `F[_]` context. Its implementation passes to `flatMapF` a function value,
mapping a `b: B` to `F.map(g(b))(Right.apply)`.

- In `flatMap` - the other of the two methods required to turn `EitherT` into a monad -, the result of type `F[Either[A, D]]`
is obtained directly by accessing `value` on the `EitherT[F, A, D]` result of the function parameter `g`.

2. A nicely symmetric method is `biflatMap`, which is akin to the right-biased `flatMap` method, but can map in both the
   "left" and the "right" case:

```Scala
def biflatMap[C, D](f: A => EitherT[F, C, D], g: B => EitherT[F, C, D])(implicit F: FlatMap[F]): EitherT[F, C, D] =
  flatTransform(_.fold(f(_).value, g(_).value))
```

Again, the argument to `flatTransform` is an anonymous function which invokes `fold` on an `Either[A, B]` receiver: in either
the "left" or the "right" case, the result of type `F[Either[C, D]]` is obtained directly by accessing `value` on either the
result of the function parameter, respectively, `f` or `g`.

3. Another symmetric `biSemiflatMap` method combines `leftSemiflatMap` and `semiflatMap` together:

```Scala
def biSemiflatMap[C, D](f: A => F[C], g: B => F[D])(implicit F: FlatMap[F]): EitherT[F, C, D] =
  flatTransform(EitherUtil.foldEF(_)(f, g))
```

The two function parameters `f` and `g` each map to a type lifted in the `F[_]` context.

So - one might guess - the definition of the `leftSemiflatMap` method is:

```Scala
def leftSemiflatMap[D](f: A => F[D])(implicit F: Monad[F]): EitherT[F, D, B] =
  biSemiflatMap(f, F.pure)
```

using a typeclass instance `Monad[F]` - again required as an `Applicative[F]` (`F.pure`) and a `FlatMap[F]` (`biSemiflatMap`).

Thus, it is also possible to re-implement the right-biased `semiflatMap` method in terms of `biSemiflatMap` as:

```Scala
def semiflatMap[D](f: B => F[D])(implicit F: Monad[F]): EitherT[F, A, D] =
  biSemiflatMap(F.pure, f)
```

4. The `leftFlatMap` method mirrors the right-biased `flatMap` method:

```Scala
def leftFlatMap[BB >: B, C](f: A => EitherT[F, C, BB])(implicit F: Monad[F]): EitherT[F, C, BB] =
  flatTransform(_.fold(f(_).value, Right.apply[C, BB] andThen F.pure))
```

Implementing `flatMap` and `leftFlatMap` in terms of `biflatMap` is also possible (ugly hinting the type checker):

```Scala
def flatMap[D](f: B => EitherT[F, A, D])(implicit F: Monad[F]): EitherT[F, A, D] =
  biflatMap(Left.apply[A, D] andThen F.pure[Either[A, D]] andThen EitherT.apply, f)

def leftFlatMap[BB >: B, C](f: A => EitherT[F, C, BB])(implicit F: Monad[F]): EitherT[F, C, BB] =
  biflatMap(f, Right.apply[C, BB] andThen F.pure[Either[C, BB]] andThen EitherT.apply)
```

5. There are three "tap" methods - `semiflatTap`, `leftSemiflatTap`, `biSemiflatTap` - which are straightly implemented in
   terms of their corresponding `*flatMap` methods - `semiflatMap`, `leftSemiflatMap`, `biSemiflatMap` -, by modifying their
   function parameter(s) via `F.tapF` before being passed as argument(s) to the latter:

```Scala
def semiflatTap[C](f: B => F[C])(implicit F: Monad[F]): EitherT[F, A, B] =
  semiflatMap(F.tapF(f))

def leftSemiflatTap[C](f: A => F[C])(implicit F: Monad[F]): EitherT[F, A, B] =
  leftSemiflatMap(F.tapF(f))

def biSemiflatTap[C, D](fa: A => F[C], fb: B => F[D])(implicit F: FlatMap[F]): EitherT[F, A, B] =
  biSemiflatMap(F.tapF(fa), F.tapF(fb))
```

where `tapF` is a `Functor` method:

```Scala
def tapF[A, B](f: A => F[B]): A => F[A] = { a => as(f(a), a) }
```

similar with `lift`, that takes a function `f: A => F[B]` to another function which - given an argument `a: A` - `map`s the
function `f` and taps the result to "purified" `a`.

6. [recoverWith](#methods-related-to-errors) pattern matches an `Either` passed by `flatTransform`.

Methods corresponding to `Either`
---------------------------------

The first group of methods is made of: `fold`, `foldF`, `isLeft`, `isRight`, `swap`, `getOrElse`, `getOrElseF`, `getOrRaise`,
`orElse`, `valueOr`, `valueOrF`, and `merge`. Except `orElse`, these methods' return types are lifted strictly into `F[_]`.

The methods ending in `F` use a `FlatMap[F]` typeclass instance, the others use a `Functor[F]` typeclass instance;
`getOrElseF` and `valueOrF` use a `Monad[F]` typeclass instance, while `getOrRaise` uses a `MonadError[F]` typeclass instance.

The two methods `fold` and `foldF` are heavily used - often by composing function parameters - in many other methods so not to
repeat the same sequence of - (1) unwrapping `value`, (2) `Either#fold`ing, (3) wrapping back in the `F[_]` context:

```Scala
def fold[C](fa: A => C, fb: B => C)(implicit F: Functor[F]): F[C] =
  F.map(value)(_.fold(fa, fb))

def foldF[C](fa: A => F[C], fb: B => F[C])(implicit F: FlatMap[F]): F[C] =
  F.flatMap(value)(_.fold(fa, fb))
```

Methods `isLeft`, `isRight`, and `getOrElse` just do `F.map`:

```Scala
def isLeft(implicit F: Functor[F]): F[Boolean] =
  F.map(value)(_.isLeft)
def isRight(implicit F: Functor[F]): F[Boolean] =
  F.map(value)(_.isRight)
def getOrElse[BB >: B](default: => BB)(implicit F: Functor[F]): F[BB] =
  F.map(value)(_.getOrElse(default))
```

As [mentioned](#methods-based-on-transform), `swap` uses `transform`:

```Scala
def swap(implicit F: Functor[F]): EitherT[F, B, A] = transform(_.swap)
```

`getOrElseF` resorts to `foldF`, with parameters the `default` as constant, and `F.pure`:

```Scala
def getOrElseF[BB >: B](default: => F[BB])(implicit F: Monad[F]): F[BB] =
  foldF(_ => default, F.pure)
```

The `orElse` method requires just an `Apply[F]` typeclass instance, doing an `F.map2` with third parameter a fully anonymous
function obtained from the `Either#orElse` method:

```Scala
def orElse[AA >: A, BB >: B](default: EitherT[F, AA, BB])(implicit F: Apply[F]): EitherT[F, AA, BB] =
  EitherT(F.map2(value, default.value)(_.orElse(_)))
```

The `valueOr`, `valueOrF`, and `merge` methods simply resort to `fold` or `foldF`:

```Scala
def valueOr[BB >: B](f: A => BB)(implicit F: Functor[F]): F[BB] =
  fold(f, identity)
def valueOrF[BB >: B](f: A => F[BB])(implicit F: Monad[F]): F[BB] =
  foldF(f, F.pure)
def merge[AA >: A](implicit ev: B <:< AA, F: Functor[F]): F[AA] =
  fold(identity, ev)
```

The second group of methods is made of `forall` and `exists`, which correspond to the same `Either` methods:

```Scala
def forall(f: B => Boolean)(implicit F: Functor[F]): F[Boolean] =
  F.map(value)(_.forall(f))
def exists(f: B => Boolean)(implicit F: Functor[F]): F[Boolean] =
  F.map(value)(_.exists(f))
```

Methods related to errors
-------------------------

The names of the methods `getOrRaise`, `recover`, `recoverWith` exist also in the API of
[`ApplicativeError`](http://typelevel.org/cats/typeclasses/applicativemonaderror.html#applicative-error), while
the names of the methods `rethrowT`, `ensure`, `ensureOr` exist also in the API of
[`MonadError`](http://typelevel.org/cats/typeclasses/applicativemonaderror.html#monaderror).

The `getOrRaise` method maps constantly a left-value to an arbitrary error `e: E` lifted into `F` with `F.raiseError`, unless
otherwise there is a right-value:

```Scala
def getOrRaise[E](e: => E)(implicit F: MonadError[F, ? >: E]): F[B] =
  getOrElseF(F.raiseError(e))
```

The `recover` and `recoverWith` methods are the equivalent of `map` and `flatMap`, but for errors.

As [mentioned](#methods-based-on-transform), `recover` uses `transform`:

```Scala
def recover(pf: PartialFunction[A, B])(implicit F: Functor[F]): EitherT[F, A, B] =
  transform {
    case Left(a) if pf.isDefinedAt(a) => Right(pf(a))
    case eab => eab
  }
```

to allow `pf` swap from a `Left(a)` - if defined at `a: A` - to `Right(pf(a))`.

As [mentioned](#methods-based-on-flattransform), `recoverWith` uses `flatTransform`:

```Scala
def recoverWith(pf: PartialFunction[A, EitherT[F, A, B]])(implicit F: Monad[F]): EitherT[F, A, B] =
  flatTransform {
    case Left(a) if pf.isDefinedAt(a) => pf(a).value
    case other                        => F.pure(other)
  }
```

to allow `pf` swap from a `Left(a)` - if defined at `a: A` - to `pf(a).value: F[Either[A, B]]`, which is an `Either` lifted
in the `F[_]` context while in the `F[_]` context, and which `flatTransform` knows how to "flatten".

The method `ensure` resorts to `ensureOr`, which, as [mentioned](#methods-based-on-transform), uses `transform`:

```Scala
def ensure[AA >: A](onFailure: => AA)(f: B => Boolean)(implicit F: Functor[F]): EitherT[F, AA, B] =
  ensureOr(_ => onFailure)(f)
def ensureOr[AA >: A](onFailure: B => AA)(f: B => Boolean)(implicit F: Functor[F]): EitherT[F, AA, B] =
  transform {
    case l @ Left(_)  => l
    case r @ Right(b) => if (f(b)) r else Left(onFailure(b))
  }
```

A left-value remains unchanged, whereas a `Right(b: B)` remains unchanged only if `f(b)` is false, when it is swapped to
`Left(onFailure(b))`.

Lastly, the `rethrowT` method almost identifies with `MonadError#rethrow`:

```Scala
def rethrowT(implicit F: MonadError[F, ? >: A]): F[B] =
  F.rethrow(value)
```

Traversing and folding methods
------------------------------

The definition of `traverse` might _seem_ a little complicated:

```Scala
def traverse[G[_], D](g: B => G[D])(implicit F: Traverse[F], G: Applicative[G]): G[EitherT[F, A, D]] =
  G.map(F.compose(using Traverse[Either[A, *]]).traverse(value)(g))(EitherT.apply)
//      111111111111111111111111111111111111111
//                                             2222222222222222222
//33333333333333333333333333333333333333333333333333333333333333333333333333333333
```

but it consists of three easy steps.

1. The _composition_ of the typeclass instances of the `Traverse` typeclass - for `F[_]` -, with that for `Either[A, *]`:

```Scala
package cats
package instances

object either extends ... {
  implicit def catsStdInstancesForEither[A]: Traverse[Either[A, *]] & ... =
    new Traverse[Either[A, *]] with ... {
      def traverse[G[_], B, C](fa: Either[A, B])(f: B => G[C])(implicit G: Applicative[G]): G[Either[A, C]] =
        EitherUtil.foldEF(fa)(F.pure, f)
    }
}
```

The typeclass instance `Traverse[Either[A, *]]` is right-biased, and consists in just the application of the function
parameter `f` to the right-value; be it a left-value or a right-value, the result is an `Either[A, C]` lifted in `G`.

2. The _traversal_ itself, invoked as `H.traverse[G, B, D](value)(g): G[F[Either[A, D]]]`, where `H: [α] =>> F[Either[A, α]]`
   is the composition `F.compose(using Traverse[Either[A, *]])` from (1).

2. The `F[Either[A, D]]` unlifts from `G`, wraps in `EitherT`, and then lifts back in `G`, _yielding_ a `G[EitherT[F, A, D]]`.

The `mapAccumulate` method is similar in form with `traverse` and akin to `map`:

```Scala
def mapAccumulate[S, C](init: S)(f: (S, B) => (S, C))(implicit F: Traverse[F]): (S, EitherT[F, A, C]) = {
  val (snext, vnext) = F.compose(using Traverse[Either[A, *]]).mapAccumulate(init, value)(f)
//                     111111111111111111111111111111111111111 22222222222222222222222222222
  (snext, EitherT(vnext))
//        33333333333333
}
```

but it keeps state, and it consists in three easy steps:

1. The _composition_ of the typeclass instances of the `Traverse` typeclass - for `F[_]` -, with that for `Either[A, *]`.

1. The _`mapAccumulate`-ing_ itself, invoked as `H.mapAccumulate(init, value)(f): (S, F[Either[A, C]])`, where
   `H: [α] =>> F[Either[A, α]]` is the composition `F.compose(using Traverse[Either[A, *]])` from (1).

1. The wrapping of `F[Either[A, C]]` from (2) in `EitherT`.

The two methods `foldLeft` and `foldRight` are similar: they make the composition `F.compose(using Foldable[Either[A, *]])`
(where the following snippet:

```Scala
package cats
package instances

object either extends ... {
  implicit def catsStdInstancesForEither[A]: Traverse[Either[A, *]] & ... =
    new Traverse[Either[A, *]] with ... {
      def foldLeft[B, C](fa: Either[A, B], c: C)(f: (C, B) => C): C =
        fa.fold(_ => c, f(c, _))
      def foldRight[B, C](fa: Either[A, B], lc: Eval[C])(f: (B, Eval[C]) => Eval[C]): Eval[C] =
        fa.fold(_ => lc, f(_, lc))
    }
}
```

defines the `Foldable[Either[A, *]]` typeclass instance), on which receiver they invoke `foldLeft`, respectively, `foldRight`,
passing the same arguments as their parameters - besides `value`:

```Scala
def foldLeft[C](c: C)(f: (C, B) => C)(implicit F: Foldable[F]): C =
  F.compose(using Foldable[Either[A, *]]).foldLeft(value, c)(f)
def foldRight[C](lc: Eval[C])(f: (B, Eval[C]) => Eval[C])(implicit F: Foldable[F]): Eval[C] =
  F.compose(using Foldable[Either[A, *]]).foldRight(value, lc)(f)
```

The `bitraverse` method, unlike `traverse`, cannot make a composition, so

1. an anonymous function is formed that `bitraverse`s the unwrapped value `Either[A, B]` with the typeclass instance
`Bitraverse[Either]` using parameters `f` and `g` as arguments,

2. `F.traverse` has arguments the `value` and the anonymous function from (1),

2. identically with step (3) for `traverse`, unwrap, and double-wrap takes place:

```Scala
def bitraverse[G[_], C, D](f: A => G[C], g: B => G[D])(implicit F: Traverse[F], G: Applicative[G]): G[EitherT[F, C, D]] =
  G.map(F.traverse(value)(Bitraverse[Either].bitraverse(_)(f, g)))(EitherT.apply)
```

`to*` methods
-------------

The `toOption` and `toIor` methods convert the `F`-lifted `Either` to an
[`OptionT`](https://github.com/sjbiaga/kittens/blob/main/mt-3-OptionT/README.md#optiont), respectively, an
[`IorT`](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md#iort):

```Scala
def toOption(implicit F: Functor[F]): OptionT[F, B] =
  OptionT(F.map(value)(_.toOption))
```

The method `toValidated` is similar, but the return type is `F[Validated[A, B]]`; the other two `toValidatedNel` (non-empty
list) and `toValidatedNec` (non-empty chain) are alike - allowing to collect the "invalid results" to, respectively, a
`NonEmptyList` and a `NonEmptyChain`.

A separate method `withValidated`, applies an `f` to a `Validated` (whose "invalid" type `A` may be aa collection) type, and
then back to an `EitherT` again, thus allowing to "momentarily" accumulate errors:

```Scala
def withValidated[C, D](f: Validated[A, B] => Validated[C, D])(implicit F: Functor[F]): EitherT[F, C, D] =
  EitherT(F.map(toValidated)(f andThen (_.toEither)))
```

The `toNested` method is direct, as `EitherT` nests an `Either[A, B]`:

```Scala
def toNested: Nested[F, Either[A, *], B] = Nested[F, Either[A, *], B](value)
```

The `toNestedValidated`, `toNestedValidatedNel`, and  `toNestedValidatedNec` methods:

```Scala
def toNestedValidated(implicit F: Functor[F]): Nested[F, Validated[A, *], B] =
  toNestedV(Validated.fromEither)
def toNestedValidatedNel(implicit F: Functor[F]): Nested[F, ValidatedNel[A, *], B] =
  toNestedV(_.fold(Validated.invalidNel, Validated.valid))
def toNestedValidatedNec(implicit F: Functor[F]): Nested[F, ValidatedNec[A, *], B] =
  toNestedV(_.fold(Validated.invalidNec, Validated.valid))
```

all resort to a `private` convenience method `toNestedV`:

```Scala
@inline def toNestedV[C, D](f: Either[A, B] => Validated[C, D])(implicit F: Functor[F]): Nested[F, Validated[C, *], D] =
  Nested(F.map(value)(f))
```

Other methods
-------------

The comparison methods `compare`, `partialCompare`, and `===`, require an implicit typeclass instance, respectively, for
`Order[F[Either[A, B]]]`, for `PartialOrder[F[Either[A, B]]]`, and for `Eq[F[Either[A, B]]]`; thus the lifting into `F`
cannot be dropped, because these methods return, respectively, an `Int`, a `Double`, and a `Boolean`.

The `combine` method can "combine" the right values of `this` and `that`, using a `Semigroup[B]`, unless either is a left:

```Scala
def combine(that: EitherT[F, A, B])(implicit F: Apply[F], B: Semigroup[B]): EitherT[F, A, B] =
  EitherT(
    F.map2(this.value, that.value) {
      case (Right(b1), Right(b2)) => Right(B.combine(b1, b2))
      case (left @ Left(_), _)    => left
      case (_, left @ Left(_))    => left
    }
  )
```

`applyAlt`, `mapK`

Methods from the companion object
---------------------------------

Typeclass instances
-------------------

From the methods `===`, `partialCompare`, and `compare`, there are three typeclass instances: respectively, for
`Eq[EitherT[F, L, A]]`, `PartialOrder[EitherT[F, L, A]]`, and `Order[EitherT[F, L, A]]`, given `implicit` typeclass instances
for, respectively, `Eq[F[Either[L, A]]]`, `PartialOrder[F[Either[L, A]]]`, and `Order[F[Either[L, A]]]`.

Given an `implicit` `Monoid[F[Either[L, A]]]` typeclass instance, there is a `Monoid[EitherT[F, L, A]]` typeclass instance.

There are `Traverse[EitherT[F, L, *]]` and `Bitraverse[EitherT[F, *, *]]` typeclass instances, in both cases, given an
`implicit` `Traverse[F]` typeclass instance, from the [traversing and folding methods](#traversing-and-folding-methods).

There is a `Bifunctor[EitherT[F, *, *]]` typeclass instance given an `implicit` `Functor[F]` typeclass instance, based on the
`bimap` method. And of course a `Functor[EitherT[F, L, *]]` typeclass instance, given an `implicit` `Functor[F]` typeclass
instance, based on the `map` method.

Extending the latter, there is a `Monad[EitherT[F, L, *]]` typeclass instance, given an `implicit` `Monad[F]` typeclass
instance, based on the `flatMap` method. The `tailRecM` method is more laborious than `pure`:

```Scala
implicit val F: Monad[F]

def pure[A](a: A): EitherT[F, L, A] = EitherT.pure(a)

def tailRecM[A, B](a: A)(f: A => EitherT[F, L, Either[A, B]]): EitherT[F, L, B] =
  EitherT {
    F.tailRecM(a) {
      (
      { (f(_: A).value): A => F[Either[L, Either[A, B]]] } andThen
        F.lift {
          case Left(l)         => Right(Left(l))
          case Right(Left(a))  => Left(a)
          case Right(Right(b)) => Right(Right(b))
        }
      ): A => F[Either[A, Either[L, B]]]
    }
  }
```

but it can be seen that it resorts to the homonym method invoked directly on the typeclass instance `F: Monad[F]`; the
function parameter `f` is transformed into a function argument of type `A => F[Either[A, Either[L, B]]]`. The type of
`F.lift` is `F[Either[L, Either[A, B]]] => F[Either[A, Either[L, B]]]`, which means that its function argument has type
`Either[L, Either[A, B]] => Either[A, Either[L, B]]`; in this light, the pattern matching of this function is clearer:

- the recursion continues only in case of `Right(Left(a))`

- the recursion ends with an `Either[L, B]` value, which is lifted in `F`, and then this is wrapped in an `EitherT`.

Depending on whether (left) type `L` is seen as the error type or not, there are two typeclass instances of the `MonadError`
typeclass:

1. `MonadError[EitherT[F, L, *], E]` "extending" the previous `Monad[EitherT[F, L, *]]` typeclass instance, given an
   `implicit val F: MonadError[F, E]` typeclass instance, defines only `handleErrorWith` and `raiseError`.

1. `MonadError[EitherT[F, L, *], L]` "extending" the previous `Monad[EitherT[F, L, *]]` typeclass instance, identifies the
   error type with `L`, and hence can access and/or provide it:

```Scala
def handleErrorWith[A](fea: EitherT[F, L, A])(f: L => EitherT[F, L, A]): EitherT[F, L, A] =
  fea.flatTransform {
    case Left(e)      => f(e).value
    case r @ Right(_) => F.pure(r)
  }
override def handleError[A](fea: EitherT[F, L, A])(f: L => A): EitherT[F, L, A] =
  fea.flatTransform {
    case Left(e)      => F.pure(Right(f(e)))
    case r @ Right(_) => F.pure(r)
  }
def raiseError[A](e: L): EitherT[F, L, A] = EitherT.left(F.pure(e))
```

Given the type parameters `M[_]: Monad` (and `E: Semigroup`), there is given the following typeclass instance of the
`Parallel` typeclass:

```Scala
new Parallel[EitherT[M, E, *]] {
  type F[x] = Nested[M, Validated[E, *], x]

  def applicative: Applicative[Nested[M, Validated[E, *], *]] = ???

  def monad: Monad[EitherT[M, E, *]] = ???
}
```

being possible to continue "`sequential`ly" from a `Nested[M, Validated[E, *], A]` with an `EitherT[M, E, A]`, or, the
opposite, to continue "in `parallel`" from an `EitherT[M, E, A]` with a `Nested[M, Validated[E, *], A]`:

```Scala
type Parallelʹ[A] = Nested[M, Validated[E, *], A]  // not in the original
type Sequentialʹ[A] = EitherT[M, E, A]             // not in the original

def sequential: Parallelʹ ~> Sequentialʹ =
  new (Parallelʹ ~> Sequentialʹ) {
    def apply[A](nested: Parallelʹ[A]): Sequentialʹ[A] =
      EitherT(Functor[M].map(nested.value)(_.toEither))
  }

def parallel: Sequentialʹ ~> Parallelʹ =
  new (Sequentialʹ ~> Parallelʹ) {
    def apply[A](eitherT: Sequentialʹ[A]): Parallelʹ[A] =
      Nested(eitherT.toValidated(using Functor[M]))
  }
```

Note that `Nested[M, Validated[E, *], *]` is a pseudo "monad transformer" for `Validated` (which is not a monad, it does not
have `flatMap`). Also note that the context bound `M[_]: Monad` is required because `M[_]` must be a `Functor` as well as an
`Applicative` - an "applicative functor", which is another term for "monad".

A typeclass instance of the [`Defer`](https://github.com/sjbiaga/kittens/blob/main/recursion-4-Defer/README.md) typeclass
asks for an `implicit` `F; Defer[F]` typeclass instance in scope. Given the `fa: => EitherT[F, L, A]` parameter, the method
`defer` is invoked with receiver `F` and argument `fa.value`. This argument uses `fa` which is a call-by-name parameter, but
the `defer` method is also passed a call-by-name argument, so `fa.value` will not be evaluated: the call-by-name flavor of
the `fa` parameter continues in the argument `fa.value`:

```Scala
implicit def ... (implicit F: Defer[F]): ... =
  new Defer[EitherT[F, L, *]] {
    def defer[A](fa: => EitherT[F, L, A]): EitherT[F, L, A] =
      EitherT(F.defer(fa.value))
  }
```

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-3-OptionT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md)
