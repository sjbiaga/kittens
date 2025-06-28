package Exercise_07_6

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

    def foldRightʹ[U](lb: Eval[U])(f: (T, Eval[U]) => Eval[U]): Eval[U] =
      def loop(it: Node[T]): Eval[U] =
        if it eq null
        then
          lb
        else
          f(it.head, Eval.defer { loop(it.tail) })
      Eval.defer { loop(node) }

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
