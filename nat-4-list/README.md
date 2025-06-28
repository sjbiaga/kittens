[First](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/eval-2-expr-tree/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md)

Lesson 06: Natural Transformations (cont'd)
===========================================

Exercise 06.7
-------------

Inside an object `ʹ`, implement an immutable `List` type with a pre-computed `size`, using a linked list of `Node`s, and with
efficient implementations of `foreach`, `map`, `flatMap` and `flatten` (and also of the other main operators):

```Scala
import scala.annotation.unchecked.uncheckedVariance

object ʹ:

  // because constructor is private, Nil is unique
  class List[+T] private (private val node: List.Node[T], val size: Int) extends IterableOnce[T]:

    import List.*

    override val knownSize: Int = size

    override def iterator: Iterator[T]

    override def toString: String = "List(" + node + ")"

    def ::[S >: T](head: S): List[S] = ???         // cons
    def :::[S >: T](that: List[S]): List[S] = ???  // concat
    def :+[S >: T](last: S): List[S] = ???         // append
    def head: T = ???
    def tail: List[T] = ???
    def foldLeft[A](ini: A)(acc: (A, T) => A): A = ???
    def foldRight[A](ini: A)(acc: (T, A) => A): A = ???  // use `cats.Eval` for stack safety

    def foreach(f: T => Unit): Unit = ???
    def map[U](f: T => U): List[U] = ???
    def flatMap[U](f: T => List[U]): List[U] = ???
    def flatten[U](implicit ev: T <:< List[U]): List[U] = ???

    def toList: scala.collection.immutable.List[T] = ???

  object List:

    def apply[T](xs: T*): List[T] =
      xs.foldRight(Nil: List[T])(_ :: _)

    private def unapply[T](self: List[T]): Option[(Node[T], Int)] =
      if self.size eq 0 then None
      else Some((self.node, self.size))

    private final case class Node[+T](head: T, var tail: Node[T @uncheckedVariance]):

      override def toString: String =
        @tailrec
        def show(self: Node[T], res: String): String =
          val head = res + self.head
          self.tail match
            case null => head
            case tail => show(tail, head + ",")
        show(this, "")

      ...

      def map[U](f: T => U): Node[U] = ???
      def flatMap[U](f: T => List[U]): (Node[U], Int) = ???  // return (head of new list, size of new list)

    object Nil extends List[Nothing](null, 0):

      override def toString: String = "Nil"

      def unapply(self: List[?]): Option[Nil.type] =
        if self eq this then Some(this)
        else None

    object :: :
      def unapply[T](self: List[T]): Option[(T, List[T])] =
        if self.size == 0 then None
        else if self.size == 1 then Some((self.node.head, Nil))
        else
          val List(Node(head, tail), size) = self : @unchecked
          Some((head, new List(tail, size - 1)))
```

Comment about the difference between `ʹ.List` and `scala.collection.immutable.List` in terms of overhead.

Based on those operators, implement a typeclass instance `kittensʹListMonad` of the `Monad` typeclass for `ʹ.List`; and give
an implementation of a natural transformation `list` from `ʹ.List` to `scala.collection.immutable.List`, accompanied by some
examples.

[Hint: the implementation of `tailRecM` should also be stack safe, using the `cats.Eval` monad, but _not_ via the
`ʹ.List.foldRight` stack safe method.]

Solution
--------

Client code should not be able to pattern match directly on `ʹ.List` - which is why this is _not_ a `case class`. As `Nil` is
_the_ empty list object, client code should not be able to build a `ʹ.List` either - which is why the constructor is private.

The companion object `ʹ.List` defines an extractor that is used internally in the implementation of the operators - so, not
from client code. The `Node` `case class` knows how to implement:

1. `reverse` - this method, annotated with `@tailrec`, uses an accumulator used as `tail` to new nodes, which means the
   resulting `Node` is built in reverse

1. `concat` reproduces the left-hand-side linked list, taking care that the `tail` of the last node is the right-hand-side

1. `init` has a precondition that the number of nodes is at least two, and follows the same line as `concat`, only that when
   it stops, the last node will not have been reproduced

1. `last` is a straight loop until the last node

1. `map` "recreates" the linked list, applying a function to each `head` item

1. `flatMap` is a generalization of `concat`: it applies a function to each `head` item, which yields another `ʹ.List`; it
   ignores the `Nil` objects, and concatenates to the ongoing `tail` of the partial result the yielded nodes (of each
   `ʹ.List`); in the caller, if the resulting `size` is zero, the `Nil` object is returned (instead of a new empty `ʹ.List`
   object).

The `Nil` object defines an extractor which compares the selector with itself using `eq`uality comparison.

And the "uncons" extractor `::` on `ʹ.List` selectors has three cases:

1. if `size` is 0, pattern matching fails

1. if `size` is 1, it returns the `head` item and the `Nil` list

1. otherwise, it constructs a `ʹ.List` of `size - 1` from the `tail` field of the linked list `node`, which it returns
   together with the `head` item: this is where the _overhead_ occurs - whereas `scala.collection.immutable.List` does _not_
   allocate memory for uncons, the `ʹ.List` `::` extractor allocates a new object with two machine-word-size fields.

There are three principal operators that have symbolic names:

1. `::` or "cons", it prepends a new head in front of the list

1. `:::` or "concat", it concatenates the argument with `this` list

1. `:+`, it appends a new item at the end of the list, and is equivalent with `this ::: (item :: Nil)`.

Other secondary operators are `head`, `headOption`, `tail`, `last`, `lastOption`, and `init`.

There is an _overhead_ in the `scala.collection.immutable.List` implementation of the `size` operator, which counts the items.

The third kind of operators are `foldLeft`, `foldRight`, and `toList`:

1. `foldLeft` is a straight loop through all nodes, while applying an accumulator binary function

1. `foldRightʹ` is _not_ stack safe, uses a `loop` recursive method which applies the accumulator function upon the return
   from recursion, starting with the initial value as the return value in the empty list base case

1. `foldRight` invokes the "recursive" `loop` method wrapped in a `cats.Eval.defer` call-by-name method call, and thus,
   provided by the `cats.Eval` monad, is _stack safe_; the application of the accumulator binary function upon the current
   item and the result from the trampolined recursion, is wrapped also in a `cats.Eval.later` call-by-name method call, and,
   hence, stack safe; these two wrapping methods are used inside a `for`-comprehension

1. `toList` prepends the items to the `scala.collection.immutable.List` accumulator using the `scala.collection.immutable.::`
   operator, and so must start with the rightmost item, which `foldRight` does.

The three Scala monad methods - `foreach`, `map`, and `flatMap`, as well as `flatten` - are the fourth kind of operators. The
first is a straight loop as `foldLeft`; the next invoke each its counterpart in the `Node` `case class`; `flatten` is
`flatMap` for the case that there is implicit evidence that the type parameter `T` is `ʹ.List[U]` for some type `U`.

```Scala
import scala.annotation.tailrec
import scala.annotation.unchecked.uncheckedVariance

import cats.Eval

object ʹ:

  class List[+T] private (private val node: List.Node[T], val size: Int) extends IterableOnce[T]:

    import List.*

    override val knownSize: Int = size

    override def iterator: Iterator[T] =
      new Iterator[T]:
        var it = node
        override def next: T =
          val res = it.head
          it = it.tail
          res
        override def hasNext: Boolean = it ne null

    override def toString: String = "List(" + node + ")"

    def reverse: List[T] =
      this match
        case Nil => Nil
        case List(node, size) => new List(node.reverse(null), size)

    def ::[S >: T](head: S): List[S] =
      this match
        case Nil => new List(Node(head, null), 1)
        case List(tail, size) => new List(Node(head, tail), size + 1)

    def :::[S >: T](that: List[S]): List[S] =
      that match
        case Nil => this
        case _ =>
          this match
            case Nil => that
            case _ => new List(that.node.concat(this.node), that.size + this.size)

    def :+[S >: T](last: S): List[S] =
      this match
        case Nil => new List(Node(last, null), 1)
        case List(node, size) => new List(node.concat(Node(last, null)), size + 1)

    def head: T =
      headOption match
        case Some(it) => it
        case _ => throw new UnsupportedOperationException("head on empty list")

    def headOption: Option[T] =
      this match
        case Nil => None
        case List(Node(head, _), _) => Some(head)

    def init: List[T] =
      this match
        case Nil => throw new UnsupportedOperationException("init on empty list")
        case List(_, 1) => Nil
        case List(node, size) => new List(node.init, size - 1)

    def last: T =
      lastOption match
        case Some(it) => it
        case _ => throw new UnsupportedOperationException("last on empty list")

    def lastOption: Option[T] =
      this match
        case Nil => None
        case List(node, _) => Some(node.last)

    def tail: List[T] =
      this match
        case Nil => throw new UnsupportedOperationException("tail on empty list")
        case List(node, size) => new List(node.tail, size - 1)

    def foldLeft[A](ini: A)(acc: (A, T) => A): A =
      var res = ini
      var it = node
      while it ne null
      do
        res = acc(res, it.head)
        it = it.tail
      res

    def foldRightʹ[A](ini: A)(acc: (T, A) => A): A = // NOT stack safe!
      def loop(it: Node[T]): A =
        if it eq null
        then
          ini
        else
          acc(it.head, loop(it.tail))
      loop(node)

    def foldRight[A](ini: A)(acc: (T, A) => A): A =
      def loop(it: Node[T]): Eval[A] =
        if it eq null
        then
          Eval.now(ini)
        else
          for
            res <- Eval.defer { loop(it.tail) }
            a   <- Eval.later { acc(it.head, res) }
          yield
            a
      loop(node).value

    def foreach(f: T => Unit): Unit =
      var it = node
      while it ne null
      do
        f(it.head)
        it = it.tail

    def map[U](f: T => U): List[U] =
      this match
        case Nil => Nil
        case List(node, size) => new List(node.map(f), size)

    def flatMap[U](f: T => List[U]): List[U] =
      this match
        case Nil => Nil
        case List(node, _) =>
          node.flatMap(f) match
            case (_, 0) => Nil
            case (node, size) => new List(node, size)

    def flatten[U](implicit ev: T <:< List[U]): List[U] =
      flatMap(ev)

    def toList: scala.collection.immutable.List[T] =
      foldRight(scala.collection.immutable.List.empty[T]) { (it, ls) => ls.prepended(it) }

  object List:

    def apply[T](xs: T*): List[T] =
      xs.foldRight(Nil: List[T])(_ :: _)

    private def unapply[T](self: List[T]): Option[(Node[T], Int)] =
      if self.size eq 0 then None
      else Some((self.node, self.size))

    private final case class Node[+T](head: T, var tail: Node[T @uncheckedVariance]):

      override def toString: String =
        @tailrec
        def show(self: Node[T], res: String): String =
          val head = res + self.head
          self.tail match
            case null => head
            case tail => show(tail, head + ",")
        show(this, "")

      @tailrec
      final def reverse[S >: T](acc: Node[S]): Node[S] =
        val node = Node(head, acc)
        if tail eq null then node
        else tail.reverse(node)

      def concat[S >: T](that: Node[S]): Node[S] =
        if that eq null then this
        else
          val result = Node(head, that)
          var temp = result
          var it = this
          while it.tail ne null
          do
            it = it.tail
            temp.tail = Node(it.head, that)
            temp = temp.tail
          result

      def init[S >: T]: Node[S] =
        val result = Node(head, null)
        var temp = result
        var it = this.tail
        while it.tail ne null
        do
          temp.tail = Node(it.head, null)
          it = it.tail
          temp = temp.tail
        result

      def last: T =
        var node = this
        while node.tail ne null
        do
          node = node.tail
        node.head

      def map[U](f: T => U): Node[U] =
        val result = Node(f(head), null)
        var temp = result
        var it = this.tail
        while it ne null
        do
          temp.tail = Node(f(it.head), null)
          it = it.tail
          temp = temp.tail
        result

      def flatMap[U](f: T => List[U]): (Node[U], Int) =
        var size = 0

        var result: Node[U] = null
        var temp: Node[U] = null

        def append(ls: List[U]): Unit =
          if ls ne Nil then
            var it: Node[U] = ls.node
            if result eq null then
              result = Node(ls.node.head, null)
              temp = result
              it = it.tail
              size += 1

            while it ne null
            do
              temp.tail = Node(it.head, null)
              it = it.tail
              temp = temp.tail
              size += 1

        var it = this
        while it ne null
        do
          append(f(it.head))
          it = it.tail

        (result, size)

    object Nil extends List[Nothing](null, 0):
      override def toString: String = "Nil"

      def unapply(self: List[?]): Option[Nil.type] =
        if self eq this then Some(this)
        else None

    object :: :
      def unapply[T](self: List[T]): Option[(T, List[T])] =
        if self.size == 0 then None
        else if self.size == 1 then Some((self.node.head, Nil))
        else
          val List(Node(head, tail), size) = self : @unchecked
          Some((head, new List(tail, size - 1)))
```

Like the `scala.collection.immutable.List` original, the implementation of the typeclass instance `kittensʹListMonad` of the
`Monad` typeclass for `ʹ.List` is straightforward, in terms of the three operators of the fourth kind (except `foreach`):

```Scala
import cats.{ Eval, Monad, StackSafeMonad, ~> }

implicit val kittensʹListMonad: Monad[ʹ.List] =
  import ʹ.List
  import List.*
  new StackSafeMonad[List]:
    override def pure[A](x: A): List[A] = x :: Nil
    override def map[A, B](fa: List[A])(f: A => B): List[B] = fa.map(f)
    override def flatMap[A, B](fa: List[A])(f: A => List[B]): List[B] = fa.flatMap(f)
    override def flatten[A](ffa: List[List[A]]): List[A] = ffa.flatten
    // override def tailRecM[A, B](a: A)(f: A => List[Either[A, B]]): List[B] = // NOT stack safe!
    //   f(a).flatMap(_.fold(tailRecM(_)(f), _ :: Nil))
    // override def tailRecM[A, B](a: A)(f: A => List[Either[A, B]]): List[B] = // still NOT stack safe!
    //   f(a).foldRight(Nil: List[B]) {
    //     case (Left(a), bs) => tailRecM(a)(f) ::: bs
    //     case (Right(b), bs) => b :: bs
    //   }
    override def tailRecM[A, B](a: A)(f: A => List[Either[A, B]]): List[B] = // stack safe!
      def tailRecMʹ(a: A): Eval[List[B]] =
        def loop(ls: List[Either[A, B]], bs: List[B]): Eval[List[B]] =
          ls match
            case Nil =>
              Eval.now(bs)
            case Left(a) :: tl =>
              for
                _   <- Eval.Unit
                bsʹ <- tailRecMʹ(a)
                bs  <- loop(tl, bs ::: bsʹ)
              yield
                bs
            case Right(b) :: tl =>
              for
                _  <- Eval.Unit
                bs <- loop(tl, bs :+ b)
              yield
                bs
        loop(f(a), Nil)
      tailRecMʹ(a).value
```

The second _not stack safe_ implementation of `tailRecM` is quite illustrative to our purpose of describing the _stack safe_
actual implementation.

1. We will iterate pattern matching through the list `f(a)` in a recursive method `loop`, to which we make the accumulator
   `bs` a second parameter; we would like this method to be as `@tailrec`ursive as possible:

```Scala
override def tailRecM[A, B](a: A)(f: A => List[Either[A, B]]): List[B] =
  @annotation.tailrec
  def loop(ls: List[Either[A, B]], bs: List[B]): List[B] =
    ls match
      case Nil =>
        bs
      case Left(a) :: tl =>
        val bsʹ = tailRecM(a)(f)
        loop(tl, bs ::: bsʹ)
      case Right(b) :: tl =>
        loop(tl, bs :+ b)
  loop(f(a), Nil)
```

But - although entirely possible - in doing so, we have this time turned `tailRecM` into a recursive non-`@tailrec`ursive
method. So we are back where we started.

2. Let us, first, modify the return type of `loop` to be `Eval[List[B]]`:

```Scala
override def tailRecM[A, B](a: A)(f: A => List[Either[A, B]]): List[B] =
  @annotation.tailrec
  def loop(ls: List[Either[A, B]], bs: List[B]): Eval[List[B]] =
    ls match
      case Nil =>
        Eval.now(bs)
      case Left(a) :: tl =>
        val bsʹ = tailRecM(a)(f)
        loop(tl, bs ::: bsʹ)
      case Right(b) :: tl =>
        loop(tl, bs :+ b)
  loop(f(a), Nil).value
```

3. Nothing changed as to the recursive nature of `tailRecM`; second, we need to get rid of the recursive "`tailRecM(a)(f)`"
   call, by introducing a nested method with almost the same name ("`tailRecMʹ`") which - for now - does the same thing:

```Scala
override def tailRecM[A, B](a: A)(f: A => List[Either[A, B]]): List[B] =
  def tailRecMʹ(a: A): List[B] =
    @annotation.tailrec
    def loop(ls: List[Either[A, B]], bs: List[B]): Eval[List[B]] =
      ls match
        case Nil =>
          Eval.now(bs)
        case Left(a) :: tl =>
          val bsʹ = tailRecMʹ(a)  // line #09
          loop(tl, bs ::: bsʹ)    // line #10
        case Right(b) :: tl =>
          loop(tl, bs :+ b)
    loop(f(a), Nil).value
  tailRecMʹ(a)
```

4. We would want the two lines #09 and #10 in Scala to be rewritten as a "stack safe" `flatMap` operation:

```Scala
tailRecMʹ(a) >>= { bsʹ => loop(tl, bs ::: bsʹ) }
```

5. But this would mean that we would need to operate in the `Eval` monad, and thus change the return type of `tailRecMʹ` (in
   line #a below; we would also need to remove the "`@tailrec`" annotation):

```Scala
override def tailRecM[A, B](a: A)(f: A => List[Either[A, B]]): List[B] =
  def tailRecMʹ(a: A): Eval[List[B]] =                                    // line #a
    def loop(ls: List[Either[A, B]], bs: List[B]): Eval[List[B]] =
      ls match
        case Nil =>
          Eval.now(bs)
        case Left(a) :: tl =>
          tailRecMʹ(a) >>= { bsʹ => loop(tl, bs ::: bsʹ) }                // line #b
        case Right(b) :: tl =>
          loop(tl, bs :+ b)                                               // line #c
    loop(f(a), Nil)
  tailRecMʹ(a).value
```

6. Still, we have not eliminated the recursive call(s), which must be trampolined by changing line #b into:

```Scala
Eval.Unit >> tailRecMʹ(a) >>= { bsʹ => loop(tl, bs ::: bsʹ) }
```

7. We do the same for line #c:

```Scala
Eval.Unit >> loop(tl, bs :+ b)
```

Now we can rewrite the two sequences of `flatMap`s as `for`-comprehensions.

As to the natural transformations, in either direction, we can use `foldRight`, which is stack safe; but in the forward
direction we already have the `toList` method:

```Scala
def list: ʹ.List ~> List =
  new (ʹ.List ~> List):
    def apply[T](ls: ʹ.List[T]): List[T] =
      ls.toList

def listʹ: List ~> ʹ.List =
  new (List ~> ʹ.List):
    def apply[T](ls: List[T]): ʹ.List[T] =
      import ʹ.List.*
      ls.foldRight(Nil: ʹ.List[T])(_ :: _)
```

We exemplify some trivial operators, the monadic interface, the natural transformation, and finally stack safety.

```Scala
try
  import ʹ.List
  import List.*
  println(List(1, 2, 3))
  ((1 :: 2 :: Nil) ::: (3 :: Nil)).foreach(println)
  println((1 :: 2 :: 3 :: Nil).map { it => List(it + it, it * it) }.flatten)
  println {
    for
      i <- (0 :: 1 :: 2 :: 3 :: Nil).tail
      j <- (2 :: 9 :: 16 :: 0 :: Nil).init
    yield
      i * j
  }
  println(list(List((1 to 10000)*)).size)
  kittensʹListMonad.tailRecM(())(Function.const(Left(()) :: Nil))
catch
  case _: StackOverflowError =>
    ???
```

[First](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/eval-2-expr-tree/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md)
