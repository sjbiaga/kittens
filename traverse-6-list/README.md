[First](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/traverse-5-set-expr/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md)

Lesson 07: Traversable (cont'd)
===============================

Exercise 07.5
-------------

For the `ʹ.List` from [Exercise 06.7](https://github.com/sjbiaga/kittens/blob/main/nat-4-list/README.md#exercise-067), give
an implementation as a typeclass instance of the `Traverse` typeclass.

Solution
--------

In order to use methods that are private within the `cats` package, we define the `kittensʹListTraverse` typeclass instance
of `Traverse` for `ʹ.List` (we put `ʹ.List` in package `Exercise_07_5` too) in the `cats` package as well:

```Scala
package cats

import cats.syntax.traverse._

implicit val kittensʹListTraverse: Traverse[Exercise_07_5.ʹ.List] =
  import Exercise_07_5.ʹ.List
  import List._
  new Traverse[List]:
    override def foldLeft[A, B](fa: List[A], b: B)(f: (B, A) => B): B =
      fa.foldLeft(b)(f)
    override def traverse[G[_]: Applicative, A, B](fa: List[A])(f: A => G[B]): G[List[B]] =
      val G = implicitly[Applicative[G]]
      ???
```

We use an `acc`umulator initialized with the empty list (`Nil`) lifted in `G`, of type `G[List[B]]`, and try the traversal
with `foldLeft`:

```Scala
foldLeft(fa, G.pure(Nil: List[B])) { (acc, a) => ??? }
```

For each item `a`, we apply `f` on it, and try to "cons" to the `acc`umulator: this latter being lifted in `G`, we would have
to use `G.map`:

```Scala
foldLeft(fa, G.pure(Nil: List[B])) { (acc, a) => G.map(acc)(f(a) :: _) } // does not compile
```

However, `f(a)` is also lifted in `G`; had we attempted to write:

```Scala
foldLeft(fa, G.pure(Nil: List[B])) { (acc, a) => G.map(f(a)) { b => G.map(acc)(b :: _) } } // does not compile
```

perhaps we would be tempted to correct the first `G.map` into `G.flatMap`:

```Scala
foldLeft(fa, G.pure(Nil: List[B])) { (acc, a) => G.flatMap(f(a)) { b => G.map(acc)(b :: _) } } // does not compile
```

but `G` is an `Applicative`, not necessarily a `FlatMap`!

If we scrutinize when is the type constructor `G[_]` applied in the following display of types:

```Scala
foldLeft(fa, G.pure(Nil: List[B])) {
  (acc: G[List[B]], a: A) =>
    G.flatMap(f(a): G[B]) { (b: B) => G.map(acc)(b :: _) } // does not compile
}
```

we see that there are _exactly two_ occurrences - `acc: G[List[B]]` and `f(a): G[B]` - of a value wrapped in `G[_]`. Since we
know [that](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md) `map2` or `map2Eval` are implemented
(in)directly via `map` (inherited from `Functor`) and `ap` (inherited from `Apply`), it seems like having two `G[_]` values is
suitable for it:

```Scala
foldLeft(fa, G.pure(Nil: List[B])) { (acc, a) => G.map2(f(a), acc)(_ :: _) }
```

Because `FlatMap` is not apparently involved, this does not mean a `traverse`al is not a _program_. For example, `Cats` has a
typeclass instance of `Applicative` for `Eval`, which is also a `StackSafeMonad`:

```Scala
package cats

object Eval {
  implicit val catsBimonadForEval: Bimonad[Eval] & ... =
    new Bimonad[Eval] with StackSafeMonad[Eval] with ... {
      override def map[A, B](fa: Eval[A])(f: A => B): Eval[B] = fa.map(f)
      def pure[A](a: A): Eval[A] = Now(a)
      def flatMap[A, B](fa: Eval[A])(f: A => Eval[B]): Eval[B] = fa.flatMap(f)
      def extract[A](la: Eval[A]): A = la.value
      def coflatMap[A, B](fa: Eval[A])(f: Eval[A] => B): Eval[B] = Later(f(fa))
      override val unit: Eval[Unit] = Eval.Unit
      override def void[A](a: Eval[A]): Eval[Unit] = Eval.Unit
    }
}
```

So we could perfectly `traverse` a `ʹ.List` with `Eval`:

```scala
scala> ʹ.List((1 to 10000)*).traverse[Eval, Int] { it => Eval.always(it * 2) }
val res0: cats.Eval[ʹ.List[Int]] = cats.Eval$$anon$1@5532d4e
```

We know that `Eval#map2` invokes `Eval#map` which invokes `Eval#flatMap` which compiles to `Eval.FlatMap` - hence a _pure_
program, whose main task is to "cons" evens in intermediary `ʹ.List`s - triggered by `Eval#value`.

As discussed [before](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md#traverselist), `Cats` resorts to
`Traverse.traverseDirectly` when an `IterableOnce` is traversed with a `StackSafeMonad`: we do it here as well, but the
intermediary `Chain` cannot be converted directly from, because of private access to `ChainIterator`:

```Scala
import cats.data.Chain
import cats.syntax.traverse._

implicit val kittensʹListTraverse: Traverse[Exercise_07_5.ʹ.List] =
  import Exercise_07_5.ʹ.List
  import List._
  new Traverse[List]:
    override def traverse[G[_]: Applicative, A, B](fa: List[A])(f: A => G[B]): G[List[B]] =
      implicitly[Applicative[G]] match
        case G: StackSafeMonad[G] =>
          G.map(Traverse.traverseDirectly(fa)(f)(G)) { chain => List(chain.toList*) }
        case G: Applicative[G] =>
          foldLeft(fa, G.pure(Nil: List[B])) { (acc, a) => G.map2(f(a), acc)(_ :: _) } // not short circuiting!
    override def foldLeft[A, B](fa: List[A], b: B)(f: (B, A) => B): B =
      fa.foldLeft(b)(f)
```

Given the implementation of `Traverse[List]#traverse` for a `G: Applicative[G]`:

```Scala
foldLeft(fa, G.pure(Nil: List[B])) { (acc, a) => G.map2(f(a), acc)(_ :: _) }
```

let us invoke `traverse` with the following two test snippets (fail fast semantics and stack safety):

```Scala
println { // fail fast
  List((1 to 10)*)
    .traverse { n => if n % 3 == 0 then None else { println(n); Option(n * 2) } }
}

println { // stack safety
  List((1 to 10000)*)
    .traverse { n => Option(n * 2) }
}
```

Unfortunately, the first snippet (with the first power of ten) does not short circuit when `G: Applicative[G]` has fail fast
semantics: numbers are printed before and _after_ `3` as well.

Switching to `foldRight`, we are compelled to have to use `G.map2Eval`:

```Scala
implicit val kittensʹListTraverse: Traverse[Exercise_07_5.ʹ.List] =
  import Exercise_07_5.ʹ.List
  import List._
  new Traverse[List]:
    override def traverse[G[_]: Applicative, A, B](fa: List[A])(f: A => G[B]): G[List[B]] =
      implicitly[Applicative[G]] match
        ...
        case G: Applicative[G] =>
          foldRight(fa, Eval.always(G.pure(Nil: List[B]))) { // not short circuiting
            (a, acc) =>
              G.map2Eval(f(a), acc)(_ :: _)
          }.value
    override def foldRight[A, B](fa: List[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
      fa.foldRight(lb)(f)
```

Surprisingly, the same problem persists as before; as a proof that the traversal is _right to left_, numbers are `println`ed
in reverse order. This is because, although `kittensʹListTraverse.foldRight` has `Eval` in its very definition, it is
implemented in terms of the stack safe method `ʹ.List#foldRight`, yes, but not also abiding to a fail fast semantics.

---

Let us add a new method `ʹ.List#foldRightʹ` (`foldRight` "prime"):

```Scala
object ʹ:
  class List[+T] private (private val node: List.Node[T], val size: Int) extends IterableOnce[T]:
    // existing method
    def foldRight[A](ini: A)(acc: (T, A) => A): A =
      def loop(it: Node[T]): Eval[A] =
        if it eq null
        then
          Eval.now(ini)
        else
          for
            res <- Eval.defer { loop(it.tail) }      // line #11
            a   <- Eval.later { acc(it.head, res) }  // line #12
          yield
            a
      loop(node).value
    // added method
    def foldRightʹ[U](lb: Eval[U])(f: (T, Eval[U]) => Eval[U]): Eval[U] =
      def loop(it: Node[T]): Eval[U] =
        if it eq null
        then
          lb
        else
          f(it.head, Eval.defer { loop(it.tail) })   // line #23
      Eval.defer { loop(node) }
```

If we compare the existing method with the added method, observe that in the latter, in line #23, the invocation to `f`
passes as second argument an `Eval.defer` program used to _continue_ folding with `it.tail`; in the former too, in line #11,
there is an identical `Eval.defer`. But while the latter gives the opportunity to `f` to _dismiss_ the invocation to `loop`
for `it.tail`, and thus short circuit the `loop`, the former uses the `Eval.defer` unconditionally.

If, also, the invocation to `f` in line #23, returns the program to _continue_ folding with `it.tail`, this will have been
_altered_ into a `FlatMap(Defer { () => loop(it.tail) }, backlogʹ<it.head>)`. Subsequent invocations to `loop` would in turn
create `backlogʹʹ<it.tail.head>`, `backlogʹʹʹ<it.tail.tail.head>`, and so on; the `backlogʹ<it.head>` function will be applied
after all subsequent `backlog`s: as part of the traversal with `kittensʹListTraverse`, a new `ʹ.List` will be created with
each `backlog`, such that the first will also be the last applied, thus achieving _right to left_ folding.

Now, the change to `kittensʹListTraverse` is minimal: just call method `fa.foldRightʹ` from `kittensʹListTraverse.foldRight`:

```Scala
implicit val kittensʹListTraverse: Traverse[Exercise_07_5.ʹ.List] =
  import Exercise_07_5.ʹ.List
  import List._
  new Traverse[List]:
    ...
    override def foldRight[A, B](fa: List[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
      fa.foldRightʹ(lb)(f)
```

Of course, `scala.collection.immutable.List` does neither have a `foldRightʹ` method, nor its existing `foldRight` method uses
`cats.Eval`: which is why the method `foldRight` in the `cats.instances.list.catsStdInstancesForList` typeclass instance of
the `Traverse` typeclass for `scala.collection.immutable.List` implements it thus, deconstructing via pattern matching a list
in `head :: tail`, which otherwise, in `ʹ.List` has an overhead, so that is why method `foldRightʹ` was added into `ʹ.List`.

Finally, there is another way to implement `traverse`, which is how `scala.collection.immutable.List` is actually
implemented, using `Chain.traverseViaChain`:

```Scala
implicit val kittensʹListTraverse: Traverse[Exercise_07_5.ʹ.List] =
  import Exercise_07_5.ʹ.List
  import List._
  new Traverse[List]:
    override def traverse[G[_]: Applicative, A, B](fa: List[A])(f: A => G[B]): G[List[B]] =
      val G = implicitly[Applicative[G]]
      G.map(Chain.traverseViaChain {
        val as = collection.mutable.ArrayBuffer[A]()
        as ++= fa.iterator
        kernel.instances.StaticMethods.wrapMutableIndexedSeq(as)
      }(f)) { chain => List(chain.toList*) }
```

Again - in the last line above -, the intermediary `Chain` cannot be converted directly from, because of private access to
`ChainIterator`. For the conversion _to_ a `scala.collection.immutable.IndexedSeq`, the `ʹ.List#iterator` method is used,
which returns a fast `scala.collection.Iterator`.

[First](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/traverse-5-set-expr/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md)
