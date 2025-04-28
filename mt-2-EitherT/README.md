[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-3-OptionT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md)

Lesson 08: Monad Transformers (cont'd)
======================================

`EitherT`
---------

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

or alternatively, using function composition with `andThen` (and some necessary hints to the type checker):

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

- the latter's parameter is a function lifted to an `F[Either[C, D]]`, whereas the former's barely returns an `Either[C, D]`;

- `F` must be a typeclass instance of either the `Functor`, or, respectively, the `FlatMap` typeclass, for `F[_]`.

The implementations too are very simple - given the type of the parameter function `f`. Both wrap the result from application
of in a `EitherT`, and pass the same two parameters `value` and `f` to  either `F.map`, or, respectively, `F.flatMap`.

####Methods based on `transform`

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

Both `map` and  `leftMap` invoke `bimap` with the same parameters, but in a different order (and of different types). The
former is also one of the two methods required to turn `EitherT` into a monad.

2. An interesting method `subflatMap`:

```Scala
def subflatMap[D](f: B => Either[A, D])(implicit F: Functor[F]): EitherT[F, A, D] =
  transform(_.flatMap(f))
```

has a function parameter of a type appropriate to invoke the (corresponding) method `flatMap` on an (anonymous) `Either`
receiver.

3. [swap](#methods-corresponding-to-either) is another method that invokes the corresponding method `swap` on an (anonymous)
   `Either` receiver.

3. [recover](#methods-related-to-errors) and [ensureOr](#methods-related-to-errors) are other two methods that pattern match
   an `Either` passed by `transform`.

####Methods based on `flatTransform`

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

2. A nicely symmetric method is `biflatMap`, which is akin to the right-biased `flatMap` method, but can map in either the
   "left" or the "right" case:

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
`orElse`, `valueOr`, `valueOrF`, and `merge`.

The methods ending in `F` use a `FlatMap[F]` typeclass instance, the others use a `Functor[F]` typeclass instance;
`getOrElseF` and `valueOrF` use a `Monad[F]` typeclass instance, while `getOrRaise` uses a `MonadError[F]` typeclass instance.

The two methods `fold` and `foldF` are heavily used - often by composing function parameters - in many other methods so not to
repeat the same sequence of - (1) unwrapping `value` (2) `Either#fold`ing (3) wrapping back in the `F[_]` context -, except
where pattern matching (like in the `collectRight` method) is unavoidable:

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

Traversing or folding methods
-----------------------------

The definition might _seem_ a little complicated:

```Scala
def traverse[G[_], D](f: B => G[D])(implicit F: Traverse[F], G: Applicative[G]): G[EitherT[F, A, D]] =
  G.map(F.compose(using Traverse[Either[A, *]]).traverse(value)(f))(EitherT.apply)
//      111111111111111111111111111111111111111
//                                             2222222222222222222
//33333333333333333333333333333333333333333333333333333333333333333333333333333333
```

but it consists in three easy steps.

1. The composition of the typeclass instances of the `Traverse` typeclass - for `F[_]` with that for `Either[A, *]`:

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
parameter `f` on the right-value; be it a left-value or a right-value, the result is an `Either[A, C]` lifted in `G`.

2. The _traversal_ itself, invoked as `F.traverse[G, B, D](value)(g): G[F[Either[A, D]]]`.

2. The `F[Either[A, D]]` unwraps from `G`, wraps in `EitherT`, and then wraps back in `G`, _yielding_ a `G[EitherT[F, A, D]]`.

The `mapAccumulate` method is similar in form with `traverse` and akin to `map`:

```Scala
  def mapAccumulate[S, C](init: S)(f: (S, B) => (S, C))(implicit F: Traverse[F]): (S, EitherT[F, A, C]) = {
    val (snext, vnext) = F.mapAccumulate(init, value)(Traverse[Either[A, *]].mapAccumulate[S, B, C](_, _)(f))
    (snext, EitherT(vnext))
  }
```

and it consists in two steps:

1. The formation of the _mapAccumulate-ing function_: if we let `g` be
   `Traverse[Either[A, *]].mapAccumulate[S, B, C](_, _)(f)`, then we can make the ascription
   `g: (S, Either[A, B]) => (S, Either[A, C])`.

2. The _mapAccumulate-ing_ itself, invoked as `F.mapAccumulate[S, Either[A, B], Either[A, C]](init, value)(g)`.

The two methods `foldLeft` and `foldRight` are similar: they make the composition `F.compose(using Foldable[Either[A, *]])`,
on which receiver they invoke `foldLeft`, respectively, `foldRight`, with the same arguments as their parameters - besides
`value`:

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
[`OptionT`](https://github.com/sjbiaga/kittens/blob/main/mt-3-optionT/README.md#optiont), respectively, an
[`IorT`](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md#iort):

```Scala
def toOption(implicit F: Functor[F]): OptionT[F, B] =
  OptionT(F.map(value)(_.toOption))
```

The method `toValidated` is similar, but the return type is `F[Validated[A, B]]`; the other two `toValidatedNel` (non-empty
list) and `toValidatedNec` (non-empty chain) are alike - allowing to collect the "invalid results" to, respectively, a
`NonEmptyList` and a `NonEmptyChain`.

A separate method `withValidated`, applies an `f` to a `Validated` (whose "invalid" types `A`/`C` may be collections), and
then back to an `EitherT` again, thus allowing to "momentarily" accumulate errors.

```Scala
def withValidated[C, D](f: Validated[A, B] => Validated[C, D])(implicit F: Functor[F]): EitherT[F, C, D] =
  EitherT(F.map(toValidated)(f andThen (_.toEither)))
```

`toNested`, `toNestedValidated`, `toNestedValidatedNel`

Other methods
-------------

`applyAlt`, `compare`, `partialCompare`, `===`, `combine`, `mapk`

Methods from the companion object
---------------------------------

[First](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/mt-3-OptionT/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md)
