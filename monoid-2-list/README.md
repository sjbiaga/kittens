[Previous](https://github.com/sjbiaga/kittens/blob/main/monoid-1-option/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/monoid-3-string/README.md)

Lesson 05: Monoids (cont'd)
===========================

`List` `Monoid`
---------------

In order to do the same thing for `List`s, wrapping should create a singleton list, unless the identity element of
`Monoid[A]` led to the empty list for `Monoid[List[A]]`, while unwrapping must combine all the elements of the `List` via a
method named `combineAll` of the `Monoid` typeclass:

```Scala
import cats.syntax.invariant._
import cats.{ Eq, Monoid }
implicit def kittensMonoidForList[A: Monoid: Eq]: Monoid[List[A]] =
  val M = implicitly[Monoid[A]]
  val E = implicitly[Eq[A]]
  M.imap { (it: A) => if E.eqv(it, M.empty) then (Nil: List[A]) else List[A](it) }
         { (it: List[A]) => if it.isEmpty then M.empty else M.combineAll(it) }
```

Now, for example, the following are true:

```Scala
import cats.syntax.monoid._
((Nil: List[Int]) |+| List(0)) eq Nil
((Nil: List[Int]) |+| List(0, 1, 3, 7)) == List(11)
```

[Previous](https://github.com/sjbiaga/kittens/blob/main/monoid-1-option/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/monoid-3-string/README.md)
