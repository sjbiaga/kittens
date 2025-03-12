Lesson 04: Trampoline and Monads (cont'd)
=========================================

The [definition](https://scalawithcats.com/dist/scala-with-cats-1.html#what-is-a-monad) in the book “Scala with Cats” is:
"A monad is a mechanism for sequencing computations."

But in `Cats` is perhaps best to introduce the `Monad` trait as derived from `FlatMap` (with a `flatten` method) and
`Applicative` (with a `pure` method) traits, given that both extend `Apply` (with an `ap` method) which extends `Functor`
(with a `map` method): this turns any monad into an _applicative functor_. A monad inherits or implements all these five
methods: `ap`, `flatten`, `flatMap`, `map`, `pure`, any one method - except `pure` - being definable in terms of other
one/two/three.

```Scala
// Cats’ Monad methods inter-definable in terms of each other

trait Monad[F[_]] extends FlatMap[F] with Applicative[F]:
  def ap[A, B](ff: F[A => B])(fa: F[A]): F[B] = flatMap(ff)(map(fa)(_))
  def ap[A, B](ff: F[A => B])(fa: F[A]): F[B] = map(ff)(map(fa)(_)).flatten
  def flatten[A](ffa: F[F[A]]): F[A] = flatMap(ffa)(identity)
  def flatMap[A, B](fa: F[A])(fun: A => F[B]): F[B] = map(fa)(fun).flatten
  def flatMap[A, B](fa: F[A])(fun: A => F[B]): F[B] = ap(pure(fun))(fa).flatten
  def map[A, B](fa: F[A])(fun: A => B): F[B] = flatMap(fa)(fun andThen pure)
  def map[A, B](fa: F[A])(fun: A => B): F[B] = ap(pure(fun))(fa)
```

Type parameter `F[_]` here is a placeholder for the type (constructor) we want to implement a `Monad` typeclass instance of.
Next is  given an instance of `Cats`’ `Monad` for `Trampoline`: it is enough to directly implement `flatMap` and `pure` by
invoking the homologue methods in `Trampoline`, and the rest indirectly.

```Scala
implicit val kittensMonadTrampolineInstance: Monad[Trampoline] =
  new StackSafeMonad[Trampoline]:
    //override def ap[A, B](ff: Trampoline[A => B])(fa: Trampoline[A]): Trampoline[B] =
    //  flatMap(ff)(map(fa)(_))
    //override def flatten[A](ffa: Trampoline[Trampoline[A]]): Trampoline[A] =
    //  flatMap(ffa)(identity)
    override def flatMap[A, B](fa: Trampoline[A])(fun: A => Trampoline[B]): Trampoline[B] =
      fa.flatMap(fun)
    //override def map[A, B](fa: Trampoline[A])(fun: A => B): Trampoline[B] =
    //  fa.map(fun)
    override def pure[A](a: A): Trampoline[A] = Trampoline.pure(a)
```

For such methods exhibiting types (monads), Scala provides syntactic sugar as `for`-comprehensions, which by the use of a
translation scheme, are compiled down to these methods.

A simple intuition behind types with a hole is related to the `pure` method: it has a type parameter, and hence also its
return type has one, which means there is some (`case`) `class` in the closed hierarchy (`Done` for `Trampoline`) with a
parameterized constructor, and hence the `sealed trait` / `abstract class` (such as `List` or `Option`) must be parameterized
too.

[For type constructors with multiple parameters, for instance `Either[A, B]`, all but one parameter should be replaced with
types, e.g., `A` with `Throwable` in `Either[Throwable, B]`, and let

```Scala
def pure[A](a: A): Either[Throwable, A] = Right(a)
```

while all the other methods `ap`, `flatten`, `flatMap`, and `map`, should return `Left(t)` if at least one argument of type
`Either[Throwable, A]` equals `Left(t)` - this semantics is called “fail-fast”.]

Note that even if the type is `Monad[Trampoline]`, the anonymous class is a `StackSafeMonad`: this is because the `Cats`
`FlatMap` trait also declares a method named `tailRecM` not yet implemented, so it suffices to instantiate an anonymous
`StackSafeMonad` that provides a definition for it.

Now that the `Monad[Trampoline]` instance is marked `implicit`, we can `summon` it in the `apply` method of the companion
object `Monad`:

```Scala
// top snippet

import cats.Monad
import Trampoline.Done
Monad[Trampoline].flatMap[Int, Double](Done(1)) { (x: Int) =>                                       // line #a
  Monad[Trampoline].flatMap[Int => Double, Double](Done((_: Int).toDouble)) { (f: Int => Double) => // line #b
    Monad[Trampoline].map[Double, Double](Done(2.0)) { (y: Double) =>                               // line #c
      f(x) + y                                                                                      // line #d
    }
  }
}
```

or, we can use an uncluttered `for`-comprehension (the two `import`s _must_ be uncommented):

```Scala
// middle snippet

import cats.Monad
//import cats.syntax.flatMap._
//import cats.syntax.functor._

def test[F[_]](implicit M: Monad[F]) =
  for
    x <- M.pure(1)                 // line #a
    f <- M.pure((_: Int).toDouble) // line #b
    y <- M.pure(2.0)               // line #c
  yield
    f(x) + y                       // line #d
```

or the equivalent through Scala translation scheme (the "syntax" `import`s required):

```Scala
// bottom snippet

import cats.Monad
import cats.syntax.flatMap._
import cats.syntax.functor._

def test[F[_]](using M: Monad[F]): F[Double] =
  val d = (_: Int).toDouble
  M.pure(1).flatMap[Double] { (x: Int) =>      // line #a
    M.pure(d).flatMap[Double] { (f: d.type) => // line #b
      M.pure(2.0).map[Double] { (y: Double) => // line #c
        f(x) + y                               // line #d
      }
   }
}
```

Equivalent lines #a-#d in each of the three snippets (top, middle, bottom) speak a lot for themselves, but let us try to see
what happens behind the scene:

1. observe that `Done` is the result of the `Monad`’s `pure` method for the `Trampoline` type constructor; thus `Done(1)` and
   `M.pure(1)` are the same thing, but not quite:

   - evaluating `kittensMonadTrampolineInstance.pure(1)` immediately returns `Done(1)`, which further uses the `Trampoline`
     Scala monad’s methods
   - because `F[_]` is not known upon the occurrence of `M.pure(1)` in either middle or bottom snippet, the compiler turns
     this `F[Int]` into a constructor parameter of a _rich wrapper_ class, and it is this one that uses instead the
     `kittensMonadTrampolineInstance` `Cats` `Monad`’s methods (see 6. below)

1. note how the type parameters in the result of `flatMap` or `map` methods is always the same: `Double`

   – top, it occurs explicit as the second type argument
   – bottom, the return type is made explicit - `F[Double]`

1. the result of the top snippet, or of invoking `test` (either middle or bottom snippet) without a pair of empty parentheses
   equals `FlatMap(Done(1), …)` where ellipsis is a lambda; when `test()` is invoked, we know that the lambda is applied `1`;
   but the lambda is the block from #a (top or bottom): hence this function is invoked with the _argument_ equal to `1`

1. yet what else `1` becomes, if not a “parameter” `x` to - i.e., a captured value by - the other closures: hence, `x`
   switches from being an argument, to becoming a _parameter_ in other computations (albeit snippets used just “pure” values)

1. thus, if it were only for the involvement of the parameters, the computations would be _pure_; but there are also the
   arguments and how are these arrived at, for example, sizes (`Long`) or checksums (`String`) of text files from the local
   file system or downloaded from the Internet: opening file descriptors or IP ports is called a _side-effect_

1. trying to compile the method `test` from the middle snippet without the commented `imports`, will give errors: why, can be
   seen from the bottom equivalent snippet, where `flatMap` and `map` are not methods invoked on a receiver of type
   `Monad[F]`, but on a value of type `F[?]`, implicitly converted to an instance of a _rich wrapper_ class similar to the
   following `Ops`:

```Scala
package cats
package syntax
object flatMap:
  implicit class Ops[F[_], A](lhs: F[A])(implicit F: FlatMap[F]):
    def flatMap[B](rhs: A => F[B]): F[B] =
      F.flatMap[A, B](lhs)(rhs)
```

```Scala
package cats
package syntax
object functor:
  implicit class Ops[F[_], A](lhs: F[A])(implicit F: Functor[F]):
    def map[B](rhs: A => B): F[B] =
      F.map[A, B](lhs)(rhs)
```

6. (cont'd)
   and turned into its constructor parameter; the latter instance _is_ the receiver for the syntactic sugar methods
   `Ops#flatMap` or `Ops#map`, whose each implementation eventually invokes the `Monad[F]` typeclass’ corresponding method
   (through the implicit parameter `F`): just as applying the Scala translation scheme for monads requires them in the bottom
   snippet, the commented imports are also required for the middle snippet

6. note that in (6) `Monad[F]` is both a subtype of `FlatMap[F]` and of `Functor[F]`, which is why either `Ops` instantiates
   with an `implicit` `Monad[F]`, too

6. Scala can apply the translation scheme for monads with `flatMap` and `map` from _different_ `Ops`, because `F` is _the
   same_: `Trampoline`

6. so in the `for`-comprehension from middle, we have on the left hand side of the arrows, the parameters, and on the right
   hand side, the computations of the arguments: neat, no need for nested blocks, but beware the issue with the imports.
