Lesson 05: Monoids
==================

By now it should be obvious that there is no way to learn `Cats` without a bit of Mathematics. The study of semigroups and
monoids is part of (abstract) Algebra. But these are practical too, for instance,

 - the `Reducible` trait (inheriting `Foldable`) uses a `Semigroup` for the method `reduce`; so does `NonEmptyList`:

```Scala
import cats.data.NonEmptyList
import cats.Monoid
implicitly[Monoid[Int]]
val nel = NonEmptyList.fromListUnsafe(List(1, 2, 4))
nel.reduce == 7
```

 - mapping a function `A => B` and then reducing using a `Monoid[B]` is known as `foldMap` in the `Foldable` trait:

```Scala
import cats.instances.list._
import cats.syntax.foldable._
List(1, 2, 3).foldMap(_.toString) == "123"
```

 - methods `exists` and `forall` with parameter a predicate `A => Boolean` can be implemented via `foldMap` with,
   respectively, a `Boolean` "or" monoid and a `Boolean` "and" monoid

 - endomorphisms (functions `A => A`) form a monoid with function composition as operation and the `identity` function as
   identity:

```Scala
import cats.data.NonEmptyList
import cats.Endo // type Endo[A] = A => A
import cats.MonoidK
/* implicit */ val kittensEndoMonoid: MonoidK[Endo] =
  new MonoidK[Endo]:
    def combineK[A](f: A => A, g: A => A): A => A = f andThen g
    def empty[A]: A => A = identity
val nel = NonEmptyList.fromListUnsafe(List[Int => Int](_.+(1), _.*(2)))
nel.reduce(kittensEndoMonoid.algebra).apply(3) == 8
```

`Option` `Monoid`
-----------------

`Cats` provides semigroups for primitive types, such as `Int`; all that is required is to "import" the `|+|` operation and
then use it:

```Scala
import cats.syntax.semigroup._
1 |+| 2
Some(1) |+| Some(2) // does not compile
```

This operation summons `implicit` typeclass instances for `Semigroup`; we can see what `implicit`s are available:

```Scala
import cats.Monoid
implicitly[Monoid[Int]]
implicitly[Monoid[Option[Int]]]
Option(1) |+| Some(2) // now compiles
```

But let us suppose that if the result is `Some(0)`, then as `0` is the identity for `Int`egers, we want the result to be
`None` instead. So let us create our own instance of `Monoid[Option[A]]`:

```Scala
import cats.syntax.invariant._
implicit def kittensMonoidForOption[A: Monoid]: Monoid[Option[A]] =
  Monoid[A].imap(Option.apply)(_.get)
Option(1) |+| Option(2)
Option(1) |+| None // runtime error
```

What `imap` does is that it takes two functions: one which _wraps_ an `A` into an `Option[A]` and the second which _unwraps_
the latter into the former:

```Scala
def wrap[A]: A => Option[A] = Option(_)
def unwrap[A]: Option[A] => A = _.get
```

This means that combining two `Option`s happens by `get`ting the values, combining them with a `Monoid` (for example, the
`implicitly[Monoid[Int]]`), and then creating an `Option` out of the result:

```Scala
{ ((opt1: Option[A]), (opt2: Option[A])) => wrap(unwrap(opt1) |+| unwrap(opt2)) }
```

Of course, with this `Option` monoid we _cannot_ `get` a value from `None`. Aside being said, we can find out where does the
automagically created monoid comes from:

```scala
scala> kittensMonoidForOption[Int]
val res0: cats.kernel.Monoid[Option[Int]] = cats.instances.InvariantMonoidalInstances$$anon$9@54950027
```

so, if we search the `Cats` repository, here is what we can find out:

```Scala
implicit val catsInvariantMonoidalSemigroup: InvariantMonoidal[Semigroup] = new InvariantMonoidal[Semigroup] {
  def product[A, B](fa: Semigroup[A], fb: Semigroup[B]): Semigroup[(A, B)] =
    (x, y) => fa.combine(x._1, y._1) -> fb.combine(x._2, y._2)

  def imap[A, B](fa: Semigroup[A])(f: A => B)(g: B => A): Semigroup[B] = // line #5
    (x, y) => f(fa.combine(g(x), g(y)))                                  // line #6

  def unit: Semigroup[Unit] = implicitly
}
```

We can see that the `catsInvariantMonoidalSemigroup` value is a typeclass instance for the `Semigroup` typeclass of the
`Invariant` functor (meaning `Semigroup` _is_ an `Invariant` - monoidal - functor), which we mentioned in
[Lesson 03 - `Expr` as `Functor`](https://github.com/sjbiaga/kittens/blob/main/expr-03-swap/README.md). The magic is thus in
lines #5-#6, specifically `f(fa.combine(g(x), g(y)))`: `g` represents unwrapping, while `f` - the wrapping.

The runtime error is due to _unwrapping_: we must check for `None` and use `M.empty` rather than `None.get`:

```Scala
implicit def kittensMonoidForOption[A](implicit M: Monoid[A]): Monoid[Option[A]] =
  M.imap(Option.apply) { it => if it eq None then M.empty else it.get }
Option(1) |+| None // == Some(1)
Option(0) |+| None // == Some(0) // wrong
```

We also would like `Some(0)` to be instead _wrapped_ as `None`: we need to test for equality with `M.empty` (`0` for `Int`).
Thankfully, `Cats` provides the `Eq` typeclass and typeclass instances of `Eq` for many types, so here is how we can
implement correctly the wrapping:

```Scala
import cats.Eq
implicit def kittensMonoidForOption[A](implicit M: Monoid[A], E: Eq[A]): Monoid[Option[A]] =
  M.imap { (it: A) => if E.eqv(it, M.empty) then Option.empty[A] else Option.apply[A](it) } (_.getOrElse(M.empty))
```

Now, all the following `eq`ual `None`:

```Scala
Option(0) |+| None
Option.empty |+| Option(0)
Option.empty[Int] |+| Option(0)
Option.empty[String] |+| Option("")
```

[Previous](https://github.com/sjbiaga/kittens/blob/main/nat-1-trampoline/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/monoid-2-list/README.md)
