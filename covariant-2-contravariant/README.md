Lesson 01: Covariant vs Contravariant Types (cont'd)
====================================================

Invariance
----------

We may say to an extent that _contravariant_ types `consume` data:

```Scala
trait Consumer[-T] { def consume(t: T): Unit }
```

while _covariant_ types `produce` data:

```Scala
trait Producer[+T] { def produce: T }
```

Other terminology is sink/source, but in general both may transform data, and, respectively, input (consume/sink) it as `T`
or output (produce/source) it as `T`.

Let us suppose we were given a `Factory` type - parameterised by the `T` type parameter - with both a method which `consume`s
a `T` and a method which `produce`s a `T`:

```Scala
trait Factory[T] extends Consumer[T] with Producer[T]
```

Then we can no longer restrict `Factory` to be either covariant or contravariant in `T` - it is, hence, _invariant_ in `T`.

So, let us define a "concrete" factory built around an `Int`eger value, which _consumes_ an `Int`eger by outputting the _sum_
of the value with the argument, and _produces_ an _identical_ `Integer` simply by yielding the value:

```Scala
case class C(n: Int) extends Factory[Int] {
  def consume(k: Int): Unit = println(n + k)
  def produce: Int = n
}
```

The question that poses here is how can we use or "map" a function with `T` as either domain or codomain, to the result that
another "factory" is created? The answer is plain that, for consumers we naturally `contramap` a function with _codomain_
(target) `T`, while for producers we naturally `comap` a function with _domain_ (source) `T`:

```Scala
trait Factory[T] extends Consumer[T] with Producer[T] { self =>
  def contramap[S](f: S => T): Factory[S] =
    new Factory[S] {
      def consume(s: S): Unit = self.consume(f(s))
      def produce: S = ???
    }
  def comap[U](g: T => U): Factory[U] =
    new Factory[U] {
      def consume(u: U): Unit = ???
      def produce: U = g(self.produce)
    }
}
```

Of course, we cannot implement the `produce` method if we contramap, because we can _only_ (use or) "map" `f` to _transform_
an existing _input_ of type `S` into the type `T`, and _then_ `consume` it by our preexisting factory.

```scala
scala> C(1).contramap((_: String).toInt)
val res0: Factory[String] = Factory$$anon$1@6f6c6c70

scala> res0.consume("2")
3
```

With `res0` factory - created from `C(1)` via `contramap` -, we can "_sum_" a string `"2"` with the value `1` and output it,
thus consuming them.

Nor can we implement the `consume` method if we comap, as we may _only_ have our preexisting factory `produce` something
prior, and _then_ (use or) "map" `g` to transform the type `T` into the type `U` - a post production, or final _output_.

```scala
scala> C(4).comap(_ * 2)
val res1: Factory[Int] = Factory$$anon$2@72998021

scala> res1.produce
val res2: Int = 8
```

With `res1` factory - created from `C(4)` via `comap` -, we can "_double_" the value `4` and yield `8`, thus producing them.

However, should we invoke `res0.produce` or `res1.consume(2)`, we would get a runtime exception.

Going both ways
---------------

We must still implement the missing methods:

```Scala
trait Factory[-I, +O] extends Consumer[I] with Producer[O] { self =>
  def contramap[A](f: A => I): Factory[A, O] =
    new Factory[A, O] {
      def consume(a: A): Unit = self.consume(f(a))
      def produce: O = self.produce
    }
  def comap[U](g: O => U): Factory[I, U] =
    new Factory[I, U] {
      def consume(i: I): Unit = self.consume(i)
      def produce: U = g(self.produce)
    }
}
```

We can see to our surprise that we can recover the contravariance of the `Consumer` trait and the covariance of the
`Producer` trait by using two type parameters instead of just one.

If we map "backwards" with the function `f: A => I`, the result of `contramap` knows how to consume an `A`, while producing
data reverts to the preexisting factory method (`self.produce`). Whereas, if we map "forwards" with the function `g: O => U`,
the result of `comap` knows how to produce an `U`, while consuming reverts to the preexisting factory method (`self.consume`).

So being contravariant in `-I` and covariant in `+O` means that we can define both `contramap` and `comap` with the missing
methods reverting to the preexisting factory methods.

```Scala
case class C(n: Int) extends Factory[Int, Int] {
  def consume(k: Int): Unit = println(n + k)
  def produce: Int = n
}
```

```scala
scala> C(1).contramap((_: String).toInt)
val res3: Factory[String, Int] = Factory$$anon$1@3f7bf0f6

scala> res3.consume("2")
3

scala> res3.produce
val res4: Int = 1
```

```scala
scala> C(4).comap(_ * 2)
val res5: Factory[Int, Int] = Factory$$anon$2@13da6bc9

scala> res5.consume(2)
6

scala> res5.produce
val res6: Int = 8
```

`Cats` `Profunctor` Typeclass
-----------------------------

`Factory` is known as a _profunctor_: "a `Contravariant` functor on its first type parameter and a `Functor` on its second
type parameter" (unlike a _bifunctor_ which is _covariant in both_ its type parameters). At a closer look, we can factor out
the implementations of `contramap` and `comap` into one single method, called `dimap`:

```Scala
trait Factory[-I, +O] extends Consumer[I] with Producer[O] { self =>
  def contramap[A](f: A => I): Factory[A, O] = dimap[A, O](f)(identity)
  def comap[U](g: O => U): Factory[I, U] = dimap[I, U](identity)(g)
  def dimap[A, U](f: A => I)(g: O => U): Factory[A, U] =
    new Factory[A, U]:
      def consume(a: A): Unit = self.consume(f(a))
      def produce: U = g(self.produce)
}

import cats.arrow.Profunctor

object Factory:
  implicit val kittensFactoryProfunctor: Profunctor[Factory] =
    new Profunctor[Factory]:
      def dimap[I, O, A, U](fa: Factory[I, O])(f: A => I)(g: O => U): Factory[A, U] =
        fa.dimap(f)(g)
```

We also provided the `kittensFactoryProfunctor`, a typeclass instance of the `Profunctor[F[_, _]]` typeclass for the
`Factory[_, _]` trait. We may see that the implementation is straightforward.

We can now create a `Factory` from the concrete factory `C(4)`, which sums a `String` with an `Int`eger (by consuming) and
doubles `4` (by producing):

```scala
scala> Profunctor[Factory].dimap(C(4))((_: String).toInt)(_ * 2)
val res7: Factory[String, Int] = Factory$$anon$1@29a5f924

scala> res7.consume("2")
6

scala> res7.produce
val res: Int = 8
```

[Previous](https://github.com/sjbiaga/kittens/blob/main/covariant-1-contravariant/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/queens-1-native/README.md)
