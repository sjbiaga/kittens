Lesson 05: Monoids (cont'd)
===========================

Let us see what happens in this three lines:

```Scala
import cats.Monoid
import cats.syntax.monoid._
0 |+| 1 |+| 3 |+| 7
```

When `import`ing `Monoid`, the companion object contains `implicit`s for `Monoid` instances, and when the _rich wrapper_
(syntax) class which defines the operator-method `|+|` is instantiated, it requires an `implicit` `Monoid[Int]` which it
finds in scope - among those afore mentioned.

`String` `Monoid`
-----------------

Let us now show how "`2 plus 2 does not equal 4`":

```Scala
import cats.syntax.invariant._
//import cats.instances.string._ // not needed
implicit val kittensMonoidForInt: Monoid[Int] = Monoid[String].imap(_.toInt)(_.toString)
2 |+| 2
```

So `invariant` is an object in package `syntax` which directly extends the `InvariantSyntax` trait and further indirectly the
`ToInvariantOps` trait (from the companion object `Invariant`). The latter defines an `implicit` method, in this case with
`Monoid[String]` as parameter and a typeclass instance `Invariant[Monoid]` as `implicit` parameter. The method instantiates
an `Ops` trait which is a _rich wrapper_, through an anonymous class. Thus, when the method `imap` is invoked, this rewrites
as:

```Scala
implicitly[Invariant[Monoid]].imap(cats.kernel.instances.StringMonoid@4125bc3c)(_.toInt)(_.toString)
```

where `cats.kernel.instances.StringMonoid@4125bc3c` is an object instance of the class `StringMonoid` in the
`cats.kernel.instances` package. This can be checked with:

```scala
scala> implicitly[Monoid[String]]
val res0: cats.kernel.Monoid[String] = cats.kernel.instances.StringMonoid@4125bc3c
```

The unwrapping function is `_.toInt`, which parses an `Int`eger from a `String`, while the wrapping function is `_.toString`,
which converts an `Int`eger to `String`. `2 |+| 2` is - after the _concatenation_ of "2" with "2" - hence the _number_ `22`.

[Previous](https://github.com/sjbiaga/kittens/blob/main/monoid-2-list/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/monoid-4-resolve/README.md)
