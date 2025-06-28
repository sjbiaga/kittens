[First](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/traverse-2-chain/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/traverse-4-nel/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md)

Lesson 07: Traversable (cont'd)
===============================

`Traverse[LazyList]`
--------------------

The `cats.instances.lazylist` object implements a typeclass instance `catsStdInstancesForLazyList` of the `Traverse` typeclass
for `LazyList`:

```Scala
package cats

package object instances {
  object lazylist {
    implicit val catsStdInstancesForLazyList: Traverse[LazyList] & ... =
      new Traverse[LazyList] with ... {
        def traverse[G[_], A, B](fa: LazyList[A])(g: A => G[B])(implicit G: Applicative[G]): G[LazyList[B]] =
          foldRight(fa, Eval.always(G.pure(LazyList.empty[B]))) { (a, lgsb) =>
            G.map2Eval(g(a), lgsb)(_ #:: _)                      // line #a
          }.value
        def foldRight[A, B](fa: LazyList[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
          Eval.now(fa).flatMap { s =>                            // line #b
            if (s.isEmpty)                                       // line #c
              lb                                                 // line #d
            else {
              val rhs = Eval.defer { foldRight(s.tail, lb)(f) }  // line #e
              f(s.head, rhs)                                     // line #f
            }
          }
      }
  }
}
```

The `traverse` method, together with the `foldRight` method, make an eloquent example of a _stack safe_ traversal, using
only `foldRight`, `Eval`, and `G.map2Eval`, given the `Applicative` `G`.

It uses neither `Traverse.TraverseDirectly` nor `Chain.traverseViaChain` because it is a _lazy_ collection, whereas these
methods result in a `Chain` - an eager collection. If the list is _infinite_, then inovking `value` in `traverse` will never
_halt_ (although it may be _interrupted_ by user action).

Exercise 07.2
-------------

Give an example of an infinite `LazyList` and `traverse` it so that it never halts.

Solution
--------

A [fibonacci series](https://www.amazon.com/Programming-Scala-Martin-Odersky/dp/098153161X) is defined starting from any two
numbers `a` and `b`; at any step, `a` is "cons"ed to the result of `fibonacci` for `b` and `a+b`: this latter invocation
"cons"es `b` (after `a`) to the result of `fibonacci` for `a+b` and `b+a+b`. Again, this latter invocation "cons"es `a+b`
(after `a` and `b`) to the result of `fibonacci` for `b+a+b` and `a+b+b+a+b`: so, the `LazyList` is
`a #:: b #:: a+b #:: fibonacci(b+a+b, a+b+b+a+b)`, which is correct:

```Scala
def fibonacci(a: Int, b: Int): LazyList[Int] =
  a #:: fibonacci(b, a + b)
```

We can visualize the pairs that are added to form the first component in the next pair, as well as triples with any two
consecutive elements in the series together with their sum:

```scala
scala> fibonacci(0, 1).sliding(2, 2).take(4).toList.map(_.toList)
val res0: List[List[Int]] = List(List(0, 1), List(1, 2), List(3, 5), List(8, 13))

scala> fibonacci(0, 1).sliding(3, 1).take(4).toList.map(_.toList)
val res1: List[List[Int]] = List(List(0, 1, 1), List(1, 1, 2), List(1, 2, 3), List(2, 3, 5))
```

We used `sliding` and `take` methods, both of which construct _finite_ `LazyList`s.

However when we try to `traverse` the fibonacci series, the traversal never halts.

```scala
scala> import cats.syntax.traverse.*, cats.Id

scala> fibonacci(0, 1).traverse[Id, Int](identity) // never halts, user presses Ctrl-C
^C
```

`Traverse[LazyList]` (cont'd)
-----------------------------

In the method `traverse`, a resulting `LazyList` is reconstructed in a `foldRight` traversal, from the applications of `f` to
its items; the result is actually `G[LazyList[B]]`, because of a precondition (1), an invariant (2), a constant (3), and an
optimization (4):

1. the empty list can be _lifted_ in the `G` context via `G.pure`;

1. the "cons" operator (`#::`) applied on each item - from _right to left_ - has _both_ a second argument a `LazyList` _and_
   its return type is a `LazyList`;

1. the _same_ `G` is used throughout to _unwrap_ the (second) argument and _wrap_ the result;

1. `G.map2Eval` is chosen over `G.map2`, to favour _laziness_, with its advantages: _fail fast_ semantics and trampolined
   _stack safety_.

The use of `foldRight` is implied by (4) because `Eval`s are found in its very definition, but it requires two neat tricks
to _avoid_ eager access to the `tail`:

5. it evades _pattern matching_ with `#::` by checking termination with `isEmpty` (line #c);

5. it _programs_ the "recursive" call for the `tail` (line #e).

Of course, without case (6), `foldRight` would be a recursive algorithm with no guard for accessing the `tail`. Therefore,
case (6) - wrapping the "recursive" call to `foldRight` in an `Eval.defer` - cannot be avoided because otherwise it would 
violate case (5):

```Scala
def foldRight[A, B](fa: LazyList[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
  Eval.now(fa).flatMap {
    case head #:: tail =>               // must be avoided,
      val rhs = foldRight(tail, lb)(f)  // using Eval.defer
      f(head, rhs)
    case _             =>
      lb
  }
```

The `Eval#flatMap` in line #b is there because, whereas the recursive invocation in line #e is stack safe, that is, `rhs` is
stack safe, the invocation of `f(s.head, rhs)` in line #f is not. For, consider the following infinite `rec`ursion involving
`foldRight`:

```Scala
import cats.instances.lazyList.*

val T = implicitly[Traverse[LazyList]]

lazy val rec: (Long, Eval[Long]) => Eval[Long] =
  { (a, _) => T.foldRight(LazyList(a), Eval.now(a))(rec) }

T.foldRight(LazyList(0L), Eval.later(???))(rec).value
```

Were it not for the use of `Eval#flatMap` in line #b, the recursive invocation to `rec` in line #f would blow up the stack.

There is a cooperation between line #a and line #f: applying `f` in line #f yields control to line #a; the latter further
compiles the second argument program (`rhs`) - instructing it to "cons"truct (`#::`) a `LazyList` -, and yields _it_ back to
the former, which will be the return value of `foldRight`. It is the turn of `evaluate` to take control (back): the deferred
"recursive" call in line #e will be invoked, at some point. (The first time `Eval#value` is invoked, `evaluate` is _given_
control.)

For `LazyList`, there is _only one_ possible iteration mode: from _left to right_; however, we must build a `LazyList` by
"cons"-ing from _right to left_, starting from the empty `LazyList`, without using the real stack.

When `s.isEmpty` (line #c), we are in the _last_ invocation to `foldRight`: `lb`, when `evaluate`d, it yields the empty
`LazyList[B]`, lifted into `G`. The items - mapped through `g: A => G[B]` - are "cons"ed in the reverse order, resulting in
the original order, while achieving _right to left_ folding.

If the `LazyList` is finite, `foldRight` will yield a value of type `G[LazyList[B]]` when `value` is invoked upon the result.
Otherwise, the heap will keep getting bigger, without ever _re"cons"tructing_ a `LazyList`, unless both `G` had a fail fast
semantics and some `g(a)` in line #a short-circuited.

Exercise 07.3
-------------

Extending `Applicative` with an `Applicativeʹ` trait which defines a method `map2Trampoline` - like `map2Eval` - but for the
[`Trampoline` `Monad`](https://github.com/sjbiaga/kittens/blob/main/queens-3-trampoline/README.md#trampoline-monad):

```Scala
object Trampoline:

  import cats.Applicative

  trait Applicativeʹ[F[_]] extends Applicative[F]:
    def map2Trampoline[A, B, Z](fa: F[A], lb: Trampoline[F[B]])(f: (A, B) => Z): Trampoline[F[Z]] =
      lb.map(map2(fa, _)(f))
```

extend also `Traverse` with `Traverseʹ`, by implementing two methods `traverseʹ` and `foldRightʹ`, that use, respectively,
the `Applicativeʹ` trait, and `Trampoline`. Leave the other unimplemented methods not implemented. Traverse fibonacci series
with the `Applicativeʹ[Option]`. Comment on the stack safety of, and detail the control flow of, the traversal.

Solution - Part 1
-----------------

The typeclass instance of the `Applicativeʹ` typeclass for `Option` is `kittensOptionApplicativeʹ`:

```Scala
import cats.instances.option.catsStdInstancesForOption

implicit val kittensOptionApplicativeʹ: Applicativeʹ[Option] =
  new Applicativeʹ[Option]:
    override def pure[A](x: A): Option[A] =
      catsStdInstancesForOption.pure(x)
    override def ap[A, B](ff: Option[A => B])(fa: Option[A]): Option[B] =
      catsStdInstancesForOption.ap(ff)(fa)

    override def map2Trampoline[A, B, Z](fa: Option[A], lb: Trampoline[Option[B]])(f: (A, B) => Z): Trampoline[Option[Z]] =
      fa match
        case None => Trampoline.pure(None)
        case Some(a) =>
          lb.map {
            case Some(b) =>
              Some(f(a, b))
            case None =>
              None
          }
```

Solution - Part 2
-----------------

The new `Traverseʹ[F[_]]` typeclass has two added methods:

```Scala
import cats.{ Applicative, Traverse }

import Trampoline.*

trait Traverseʹ[F[_]] extends Traverse[F]:
  def traverseʹ[G[_]: Applicativeʹ, A, B](fa: F[A])(f: A => G[B]): G[F[B]]
  def foldRight[A, B](fa: F[A], lb: Trampoline[B])(f: (A, Trampoline[B]) => Trampoline[B]): Trampoline[B]
```

The typeclass instance of the `Traverseʹ` typeclass for `LazyList` is `kittensLazyListTraverseʹ`:

```Scala
import Trampoline.Call

implicit val kittensLazyListTraverseʹ: Traverseʹ[LazyList] =
  new Traverseʹ[LazyList]:
    def traverseʹ[G[_], A, B](ga: LazyList[A])(g: A => G[B])(implicit G: Applicativeʹ[G]): G[LazyList[B]] =
      Trampoline.pure(ga).flatMap { s =>
        foldRightʹ(s, Trampoline.pure(G.pure(LazyList.empty[B]))) { (a, lgsb) =>
          G.map2Trampoline(g(a), lgsb)(_ #:: _)
        }
      }()
    def foldRightʹ[A, B](fa: LazyList[A], lb: Trampoline[B])(f: (A, Trampoline[B]) => Trampoline[B]): Trampoline[B] =
      Trampoline.pure(fa).flatMap { s =>
        if s.isEmpty
        then
          lb
        else
          val rhs = Call(foldRightʹ(s.tail, lb)(f))
          f(s.head, rhs)
      }

    override def traverse[G[_]: Applicative, A, B](fa: LazyList[A])(f: A => G[B]): G[LazyList[B]] = ???
    override def foldLeft[A, B](fa: LazyList[A], b: B)(f: (B, A) => B): B = ???
    override def foldRight[A, B](fa: LazyList[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] = ???
```

Solution - Part 3
-----------------

We give three example of traversal: first, one which succeeds and yields the first `10` fibonacci numbers; second, a fail
fast example which yields `None`; third, a test for stack safety using `100000` items:

```Scala
try

  def fibonacci(a: Long, b: Long): LazyList[Long] =
    a #:: fibonacci(b, a + b)

  println {
    val T = implicitly[Traverseʹ[LazyList]]
    T.traverseʹ[Option, Long, Long](fibonacci(0, 1).take(10))(Some(_)).get.toList
  }

  println {
    val T = implicitly[Traverseʹ[LazyList]]
    T.traverseʹ[Option, Long, Long](fibonacci(0, 1)) {
      it =>
        if it % 3 != 0
        then
          println(it)
          Some(it)
        else
          None
    }
  }

  println {
    val T = implicitly[Traverseʹ[LazyList]]
    T.traverseʹ[Option, Int, Int](LazyList((1 to 100000)*))(Option.apply)
      .get
      .size
  }

catch
  case _: StackOverflowError =>
    ???
```

[First](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/traverse-2-chain/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/traverse-4-nel/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md)
