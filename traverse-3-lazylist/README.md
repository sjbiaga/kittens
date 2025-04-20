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
        def traverse[G[_], A, B](fa: LazyList[A])(f: A => G[B])(implicit G: Applicative[G]): G[LazyList[B]] =
          foldRight(fa, Eval.always(G.pure(LazyList.empty[B]))) { (a, lgsb) =>
            G.map2Eval(f(a), lgsb)(_ #:: _)
          }.value
        def foldRight[A, B](fa: LazyList[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
          Eval.now(fa).flatMap { s =>                            // line #a
            if (s.isEmpty)                                       // line #b
              lb
            else {
              val rhs = Eval.defer { foldRight(s.tail, lb)(f) }  // line #c
              f(s.head, rhs)                                     // line #d
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
scala> import cats.syntax.traverse._, cats.Id

scala> fibonacci(0, 1).traverse[Id, Int](identity) // never halts, user presses Ctrl-C
^C
```

`Traverse[LazyList]` (cont'd)
-----------------------------

In the method `traverse`, a resulting `LazyList` is reconstructed in a `foldRight` traversal, from the applications of `f` to
its items; the result is actually `G[LazyList[B]]`, because of a precondition (1), an invariant (2), a constant (3), and an
optimisation (4):

1. the empty list can be _lifted_ in the `G` context via `G.pure`;

1. the "cons" operator (`#::`) applied on each item - from _right to left_ - has _both_ a second argument a `LazyList` _and_
   its return type is a `LazyList`;

1. the _same_ `G` is used throughout to _unwrap_ the (second) argument and _wrap_ the result;

1. `G.map2Eval` is chosen over `G.map2`, to favour _laziness_, with its advantages: _fail fast_ semantics and trampolined
   _stack safety_.

The use of `foldRight` is implied by (4) because `Eval`s are found in its very definition, but it requires three neat tricks
to _avoid_ eager access to the `tail`:

5. it _delays_ its execution by sanitizing with a `FlatMap` (line #a);

5. it evades _pattern matching_ with `#::` by checking termination with `isEmpty` (line #b);

5. it _programs_ the "recursive" call for the `tail` (line #c) rather than relaying to (5).

Of course, without _both_ (5) and (7), `foldRight` would be a recursive algorithm without any guard for accessing the `tail`,
and so - without even the need of invoking `Eval#value` - it could blow up the stack.

The delay in line #a is _eager_ - because the receiver to `flatMap` is an `Eval.now`. Therefore, case (7) - wrapping the
"recursive" call to `foldRight` in an `Eval.defer` - cannot be avoided because otherwise it would violate case (6):

```Scala
import cats.{ Applicative, Eval, Traverse }

implicit val kittensLazyListTraverse: Traverse[LazyList] =
  new Traverse[LazyList]:
    def traverse[G[_], A, B](fa: LazyList[A])(f: A => G[B])(implicit G: Applicative[G]): G[LazyList[B]] =
      foldRight(s, Eval.always(G.pure(LazyList.empty[B]))) { (a, lgsb) =>
        G.map2Eval(f(a), lgsb)(_ #:: _)
      }.value
    def foldRight[A, B](fa: LazyList[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
      Eval.now(fa).flatMap {
        case head #:: tail =>               // must be avoided,
          val rhs = foldRight(tail, lb)(f)  // using Eval.defer
          f(head, rhs)
        case _             =>
           lb
      }
```

It remains to see the rationale behind case (5); we can re-implement equivalently `kittensLazyListTraverse` by surrounding the
("recursive") calls to `foldRight` within `Eval.now(_).flatMap`:

```Scala
import cats.{ Applicative, Eval, Traverse }

implicit val kittensLazyListTraverse: Traverse[LazyList] =
  new Traverse[LazyList]:
    def traverse[G[_], A, B](fa: LazyList[A])(g: A => G[B])(implicit G: Applicative[G]): G[LazyList[B]] =
      Eval.now(fa).flatMap { s =>
        foldRight(s, Eval.always(G.pure(LazyList.empty[B]))) { (a, lgsb) =>
          G.map2Eval(g(a), lgsb)(_ #:: _)  // line #08
        }
      }.value                              // line #10
    def foldRight[A, B](fa: LazyList[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
      if fa.isEmpty                        // line #12
      then
        lb
      else
        val rhs = Eval                     // line #16
          .defer {                         // line #17
            Eval                           //
              .now(fa.tail)                // line #19
              .flatMap {                   // line #20
                foldRight(_, lb)(f)        // line #21
              }
          }
        f(fa.head, rhs)                    // line #24
```

Thus, `foldRight` has been sanitized at the call site: for the "recursive" case (lines #16-#24), an `Eval.FlatMap` is always
"wrapped" inside an `Eval.defer` (line #17). The role of line #19 is to _force_ the `tail` "now", while that of lines #20-#21
is to _delay_ the "recursive" call to `foldRight` (for "later"), hence trampolining it in line #21.

The second argument `rhs` to `f` (line #24) is assigned in line #16 to _program_ this compilation.

There is a cooperation between line #08 and line #24: applying `f` in line #24 yields control to line #08; the latter further
compiles the second argument program (`rhs`) - instructing it to "cons"truct (`#::`) a `LazyList` -, and yields _it_ back to
the former, which will be the return value of `foldRight`. It is time for `evaluate` to take control (back): the trampolined
"recursive" call in line #21 will be invoked, at some point. (The first time `Eval#value` is invoked - line #10 -, `evaluate`
is _given_ control.)

For `LazyList`, there is _only one_ possible iteration mode: from _left to right_; however, we must build a `LazyList` by
"cons"-ing from _right to left_, starting from the empty `LazyList`, without using the real stack.

When `fa.isEmpty` (line #12), we are in the _last_ invocation to `foldRight`: `lb`, when `evaluate`d, it yields the empty
`LazyList[B]`, lifted into `G`. The items - mapped through `g: A => G[B]` - are "cons"ed in the reverse order, resulting in
the original order, while achieving _right to left_ folding.

If the `LazyList` is finite, `foldRight` will yield a value of type `G[LazyList[B]]` when `value` is invoked upon the result.
Otherwise, the heap will keep getting bigger, without ever _re"cons"tructing_ a `LazyList`.

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

import Trampoline._

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
          G.map2Trampoline(g(a), lgsb)(_ #:: _)  // line #08
        }
      }()                                        // line #10
    def foldRightʹ[A, B](fa: LazyList[A], lb: Trampoline[B])(f: (A, Trampoline[B]) => Trampoline[B]): Trampoline[B] =
      if fa.isEmpty                              // line #12
      then
        lb
      else
        val rhs =                                // line #16
          Call {                                 // line #17
            Trampoline
              .pure(fa.tail)                     // line #19
              .flatMap {                         // line #20
                foldRightʹ(_, lb)(f)             // line #21
              }
          }
        f(fa.head, rhs)                          // line #24

    override def traverse[G[_]: Applicative, A, B](fa: LazyList[A])(f: A => G[B]): G[LazyList[B]] = ???
    override def foldLeft[A, B](fa: LazyList[A], b: B)(f: (B, A) => B): B = ???
    override def foldRight[A, B](fa: LazyList[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] = ???
```

With `foldRightʹ` sanitized at the call site, for the "recursive" case (lines #16-#24), a `FlatMap` is always "wrapped"
inside a `Call` (line #17). The role of line #19 is to _force_ the `tail` "now", while that of lines #20-#21 is to _delay_
the "recursive" call to `foldRightʹ` (for "later"), hence trampolining it in line #21.

The second argument `rhs` to `f` (line #24) is assigned in line #16 to _program_ this compilation.

There is a cooperation between line #08 and line #24: applying `f` in line #24 yields control to line #08; the latter further
compiles the second argument program (`rhs`) - instructing it to "cons"truct (`#::`) a `LazyList` -, and yields _it_ back to
the former, which will be the return value of `foldRightʹ`.

Assume the following implementation of `Trampoline#apply`:

```Scala
enum Trampoline[+A]:
  @annotation.tailrec
  final def apply(): A = this match
    case Done(value) =>
      value                                          // line #a
    case Call(closure) =>
      closure(())()                                  // line #b
    case FlatMap(Done(value), sequel) =>
      sequel(value)()                                // line #c
    case FlatMap(Call(closure), sequel) =>
      (closure :: sequel)(())()                      // line #d
    case FlatMap(FlatMap(self, prequel), sequel) =>
      FlatMap(self, prequel :: sequel)()             // line #e

object Trampoline:
  // Kleisli composition
  extension [A, B](prequel: A => Trampoline[B])
    inline def ::[C](sequel: B => Trampoline[C]): A => Trampoline[C] =
      prequel(_).flatMap(sequel)
```

The first time `Trampoline#apply` is invoked - line #10 -, it is _given_ control:

```Scala
FlatMap(Done(ga), { s =>
                    foldRightʹ(s, Trampoline.pure(G.pure(LazyList.empty[B]))) {
                      (a, lgsb) =>
                        G.map2Trampoline(g(a), lgsb)(_ #:: _) }
                  }
)()
```

By line #c, this reduces to:

```Scala
foldRightʹ(ga, lb) { (a, lgsb) =>
                     G.map2Trampoline(g(a), lgsb)(_ #:: _) }()
```

where `lb` is `Trampoline.pure(G.pure(LazyList.empty[B]))`. Before `apply`ing, the first invocation to `foldRightʹ` - in a
call on the stack - will assign to `rhs` in line #16 the (`Trampoline[LazyList[B]]`) value
`Call { _ => Trampoline.pure(faʹ.tail).flatMap(foldRightʹ(_, lb)(f)) }`. Through lines #24 and #08, `rhs` will further
compile into:

```Scala
FlatMap(Call { _ => Trampoline.pure(faʹ.tail).flatMap(foldRightʹ(_, lb)(f)) }, { gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))
```

where `faʹ` is `fa` in the first invocation to `foldRightʹ`, and `g(faʹ.head): G[B]` is the application of `g` to `a` from
line #08 (`a` being `faʹ.head`).
The function `{ gtl => <g(a) #:: gtl> } andThen Done(_)` is the result of `G.map2Trampoline(g(a), lgsb)(_ #:: _)`, where
`<gb #:: gtl>` represents:

1. the unwrapping of `gb: G[B]` and `gtl: G[LazyList[B]]` from `G`;

1. the application of the "cons" (`#::`) operator to these two, respective, operands;

1. the wrapping of the new `LazyList` into `G`.

Now, `apply` is given control back and it invokes itself `@tailrec`ursively; by line #d, this reduces to:

```Scala
({ _ => Trampoline.pure(faʹ.tail).flatMap(foldRightʹ(_, lb)(f)) } :: { gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))(())()
```

Applying the Kleisli composition (`::`), this will yield the function:

```Scala
{ _ => Trampoline.pure(faʹ.tail).flatMap(foldRightʹ(_, lb)(f)).flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_)) }
```

Applying unit (`()`) to this function yields (`faʹ.tail` is being accessed):

```Scala
Trampoline.pure(faʹ.tail).flatMap(foldRightʹ(_, lb)(f)).flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))
```

which reduces in two steps to:

```Scala
FlatMap(Done(faʹ.tail)
       , foldRightʹ(_, lb)(f))
  .flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))
```

and in another step to:

```Scala
FlatMap(FlatMap(Done(faʹ.tail)
               , foldRightʹ(_, lb)(f))
       , { gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))
```

Now, `apply` invokes itself `@tailrec`ursively a second time; by line #e, this reduces to:

```Scala
FlatMap(Done(faʹ.tail)
       , foldRightʹ(_, lb)(f) :: { gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))()
```

By applying the Kleisli composition (`::`), the receiver to `apply` reduces to:

```Scala
FlatMap(Done(faʹ.tail)
       , foldRightʹ(_, lb)(f).flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_)))
```

Now, `apply` invokes itself `@tailrec`ursively a third time; by line #c, this reduces to:

```Scala
foldRightʹ(faʹ.tail, lb)(f).flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))()
```

Letting `faʹʹ` be `faʹ.tail`, the second trampolined invocation to `foldRightʹ(faʹʹ, lb)(f)` yields:

```Scala
FlatMap(Call { _ => Trampoline.pure(faʹʹ.tail).flatMap(foldRightʹ(_, lb)(f)) }
       , { gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_))
```

Note that there is no `Trampoline#apply`ing here, and this latter `FlatMap` is a returned _value_, _not_ a _receiver_: we were
being called on the stack, with `apply` still awaiting to be performed (so we _cannot_ "reduce by line #d" - yet):

```Scala
FlatMap(Call { _ => Trampoline.pure(faʹʹ.tail).flatMap(foldRightʹ(_, lb)(f)) }
       , { gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_))
  .flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))()
```

which reduces to:

```Scala
FlatMap(FlatMap(Call { _ => Trampoline.pure(faʹʹ.tail).flatMap(foldRightʹ(_, lb)(f)) }
               , { gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_))
       , { gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))()
```

`apply` invokes itself `@tailrec`ursively a fourth time; by line #e, this reduces to:

```Scala
FlatMap(Call { _ => Trampoline.pure(faʹʹ.tail).flatMap(foldRightʹ(_, lb)(f)) }
       , ({ gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_)) :: ({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_)))()
```

By applying the Kleisli composition (`::`), the receiver to `apply` reduces to:

```Scala
FlatMap(Call { _ => Trampoline.pure(faʹʹ.tail).flatMap(foldRightʹ(_, lb)(f)) }
             , ({ gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_))
                 .flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_)))()
```

Only now, by line #d we have:

```Scala
({ _ => Trampoline.pure(faʹʹ.tail).flatMap(foldRightʹ(_, lb)(f)) } :: (({ gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_))
                                                                          .flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))))(())()
```

Applying the Kleisli composition (`::`) reduces to:

```Scala
({ _ => Trampoline.pure(faʹʹ.tail).flatMap(foldRightʹ(_, lb)(f)) }
   .flatMap(({ gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_))
              .flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))))(())()
```

Applying unit (`()`) to this function yields (`faʹʹ.tail` is being accessed):

```Scala
Trampoline.pure(faʹʹ.tail)
  .flatMap(foldRightʹ(_, lb)(f))
  .flatMap(({ gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_))
             .flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_)))()
```

which reduces in two steps to:

```Scala
FlatMap(Done(faʹʹ.tail)
       , foldRightʹ(_, lb)(f))
  .flatMap(({ gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_))
             .flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_)))()
```

and in another step to:

```Scala
FlatMap(FlatMap(Done(faʹʹ.tail)
               , foldRightʹ(_, lb)(f))
       , ({ gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_))
           .flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_)))()
```

Now, `apply` invokes itself `@tailrec`ursively a fifth time; by line #e, this reduces to:

```Scala
FlatMap(Done(faʹʹ.tail)
       , foldRightʹ(_, lb)(f) :: (({ gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_))
                                    .flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))))()
```

By applying the Kleisli composition (`::`), the receiver to `apply` reduces to:

```Scala
FlatMap(Done(faʹʹ.tail)
       , foldRightʹ(_, lb)(f)
           .flatMap(({ gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_))
                      .flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))))()
```

Now, `apply` invokes itself `@tailrec`ursively a sixth time; by line #c, this reduces to:

```Scala
foldRightʹ(faʹʹ.tail, lb)(f)
  .flatMap(({ gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_))
             .flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_)))()
```

Let us supposed that `faʹʹ.tail` is empty: `foldRightʹ(faʹʹ.tail, lb)(f)` yields `lb`, which gives:

```Scala
Trampoline.pure(G.pure(LazyList.empty[B]))
  .flatMap(({ gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_))
             .flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_)))()
```

that reduces in two steps to:

```Scala
FlatMap(Done(G.pure(LazyList.empty[B]))
       , ({ gtl => <g(faʹʹ.head) #:: gtl> } andThen Done(_))
           .flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_)))()
```

Now, `apply` invokes itself `@tailrec`ursively a seventh time; by line #c, this reduces to:

```Scala
Done(<g(faʹʹ.head) #:: G.pure(LazyList.empty[B])>)
  .flatMap({ gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))()
```

and in another step to:

```Scala
FlatMap(Done(<g(faʹʹ.head) #:: G.pure(LazyList.empty[B])>)
       , { gtl => <g(faʹ.head) #:: gtl> } andThen Done(_))()
```

Now, `apply` invokes itself `@tailrec`ursively an eighth time; by line #c, this reduces to:

```Scala
Done(<g(faʹ.head) #:: g(faʹʹ.head) #:: G.pure(LazyList.empty[B])>)()
```

Invoking itself `@tailrec`ursively the ninth time; by line #a, `apply` yields:

```Scala
<g(faʹ.head) #:: g(faʹʹ.head) #:: G.pure(LazyList.empty[B])>
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
