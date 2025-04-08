[Previous](https://github.com/sjbiaga/kittens/blob/main/monoid-3-string/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-08-monoidK/README.md)

Lesson 05: Monoids (cont'd)
===========================

Resolving `Monoid`s
-------------------

Let us assume we want to “add” element-wise the following nested lists, revolving to integers addition:

```Scala
List(Option(List(1)), Option(List(2, 0)), Option(List(3)) |*| List(None, Option(List(0, 2)))
```

resulting in: `List(None, Option(List(4,4)))`. Using implicits, we can do this in `Cats` through the `Monoid` typeclass.

```Scala
// An example of implicit parameters, classes, and methods

import cats.Monoid, cats.instances.int._

object Ops:
  implicit class SemigroupOps[A: Monoid] private[Ops] (lhs: A): // line #6
    def |*|(rhs: A) = implicitly[Monoid[A]].combine(lhs, rhs)

import Ops._

implicit class ListMonoid[A: Monoid] extends Monoid[List[A]]: // line #11
  def empty: List[A] = Nil
  def combine(a: List[A], b: List[A]): List[A] =
    (a zip b).map(_ |*| _) // line #14

class OptionMonoid[A: Monoid] extends Monoid[Option[A]]: // line #16
  def empty: Option[A] = None
  def combine(a: Option[A], b: Option[A]): Option[A] =
    (a zip b).map(_ |*| _) // line #19

object ListMonoid:
  implicit val listOfIntMonoid: Monoid[List[Int]] = new ListMonoid[Int]

object OptionMonoid:
  implicit def optionMonoid[A: Monoid]: Monoid[Option[A]] = new OptionMonoid[A] // line #25

import ListMonoid._, OptionMonoid._
```

We start by importing it and then we want the elements of monoids to be combined via a special syntax as the `|*|`
operator. We define an `implicit` `class` named `SemigroupOps` with just one method name `|*|`: because it is marked as
`implicit`, when a receiver calls `|*|`, this _rich wrapper_ class will be instantiated and this instance will become the
left hand side operand to the `|*|` operator. However, it wraps the receiver as parameter: when also the `rhs` has been
computed, `lhs` can be used.

Obviously, `|*|` cannot be added as a method to each type `A`: it is syntactic sugar merely, its definition revolves to the
`combine` method.

The type parameter `A: Monoid` specifies that there be an `implicit` parameter of type `Monoid[A]` to the rich wrapper. We
can use the `implicitly[Monoid[A]]` method to summon it (or even `summon[Monoid[A]]` in Scala 3). `Monoid` inheriting
`Semigroup`, the `combine` method can then be invoked with the operands `lhs` and `rhs`.

To make `List[A]` a `Monoid`, we have to provide with instances of `Monoid[List[A]]`, where for the type parameter `A`, there
must exist an instance of `Monoid[A]` as well.

To make `Option[A]` a `Monoid`, we have to provide with instances of `Monoid[Option[A]]`, where for the type parameter `A`,
there must exist an instance of `Monoid[A]` as well.

Note how lines #14 and #19 are identical. The method `zip` on lists returns pairs as many as the minimum of the two operand
lists’ sizes; while the method `zip` on options returns `None` unless both operands are non-empty: the pairs are mapped
through the `(_:A) |*| (_:A)` function literal.

In the expression we want to be evaluated:

```Scala
List(Option(List(1)), Option(List(2, 0)), Option(List(3)) |*| List(None, Option(List(0, 2)))
```

1. because of the main operator `|*|`, type `A` in line #6 is identified as `List[Option[List[Int]]]`

1. hence, the compiler tries to instantiate a `Monoid[List[Option[List[Int]]]]`, so it looks for _either_

   - an `implicit` `class` extending type `Monoid[List[Option[List[Int]]]]`, or
   - an `implicit` `val` of type `Monoid[List[Option[List[Int]]]]`, or
   - an `implicit` `def` with return type `Monoid[List[Option[List[Int]]]]`;

   however, it finds the next best thing: the `implicit` `class` `ListMonoid`, extending `Monoid[List[A]]`, with a type
   parameter `A: Monoid` - constraining an `implicit` `Monoid[Option[List[Int]]]` to be in scope: thus, type `A` in line #11,
   is identified as `Option[List[Int]]`

1. hence, the compiler tries to instantiate a `Monoid[Option[List[Int]]]`, so it looks for either

   - an `implicit` `class` extending type `Monoid[Option[List[Int]]]`, or
   - an `implicit` `val` of type `Monoid[Option[List[Int]]]`, or
   - an `implicit` `def` with return type `Monoid[Option[List[Int]]]`;

   however, because of the last `import`, it finds the next best thing: the `implicit` method `optionMonoid` with the return
   type `Monoid[Option[A]]` (which instantiates `OptionMonoid[A]` from line #16) and a type parameter `A: Monoid` - constraining an `implicit` `Monoid[List[Int]]` to be in scope: thus, type `A` in line #25 is identified as `List[Int]`

1. hence, the compiler tries to instantiate a `Monoid[List[Int]]`, so because of the `import`, it finds the `implicit` value
   `listOfIntMonoid` of type `Monoid[List[Int]]`

   - which instantiates `ListMonoid[Int]` from #11
   - by identifying the type `A` as `Int`;

   however, in `ListMonoid`, the type parameter `A: Monoid` (identified with `Int`) constrains an `implicit` `Monoid[Int]` to
   be in scope: because of the first `import`, `Cats` already provides one for us

1. now, in the reverse order, the compiler instantiates the `Monoid[Int]` (provided by `Cats`), then (4), (3), and (2); thus,
   for (2) and (4), the two instances are of the same `ListMonoid[?]` class.

Of course, we can drop `object`s `ListMonoid` and `OptionMonoid` altogether and rely only on the `implicit` `class`es in
line #11 and #16. However, as in `Cats`, the preferred way is to instantiate _anonymous_ `class`es from inside `implicit`
methods: `implicit` `class`es having public constructors can be instantiated at random.

Note that the constructor for the `SemigroupOps` `implicit` `class` in line #6 has `private[Ops]` modifier, restricting it
from being instantiated, except by the compiler in `implicit` conversions of the receivers to the `|*|` method call.

[As to the difference between `implicit` parameters and `using` clauses, the latter can mark any parameter list, whereas the
former must occur only in the last parameter list. When passing explicit parameters to `using` clauses, the keyword must
precede the arguments; otherwise, the parentheses can be completely left out, if `given` instances or `implicit` / `using`
parameters are in scope.]

[Previous](https://github.com/sjbiaga/kittens/blob/main/monoid-3-string/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-08-monoidK/README.md)
