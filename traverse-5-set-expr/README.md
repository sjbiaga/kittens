[First](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/traverse-4-nel/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/traverse-6-list/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md)

Lesson 07: Traversable (cont'd)
===============================

Exercise 07.4
-------------

Is it possible to add, subtract, multiply, or divide collections using `Expr`essions?

[Hint:
because `Set` is not traversable, we first use the `traverse` method from the typeclass instance of the `Traverse`
typeclass for `List`, as in the following `opsify` method:

```Scala
import scala.util.Random.{ nextInt, shuffle }

import Expr._

enum Op:
  case +, -, *, /, ~, `0`, `1`

def opsify(ls: List[List[Int]]): List[Expr[List[Int]]] =
  require(ls.size >= 2)
  shuffle {
    ls.traverse(identity)
      .sliding(2, 3)
      .toList
  }
  .take(2+nextInt(5))
  .zipWithIndex
  .map {
    case ((List(lhs, rhs), idx)) =>
      if idx % 2 == 0
      then
        Op.+ -> (lhs, rhs)
      else if idx % 4 == 0
      then
        Op.* -> (lhs, rhs)
      else
        Op.- -> (lhs, rhs)
  }
  .map { it =>
    val lhs = Val(it._2._1)
    val rhs = Val(it._2._2)
    it._1 match
      case Op.+ => Add(lhs, rhs)
      case Op.- => Sub(lhs, rhs)
      case Op.* => Mul(lhs, rhs)
      case Op./ => Div(lhs, rhs)
      case Op.~ => Inv(rhs)
      case Op.`0` => Zero
      case Op.`1` => One
  }
```

The argument `ls` is `traverse`d with `identity`: it will return all possible combinations, each combination being a `List`
with items from each argument sub-list:

```scala
scala> List(List(1,4),List(0,5)).traverse(identity)
val res0: List[List[Int]] = List(List(1, 0), List(1, 5), List(4, 0), List(4, 5))
```

It acts like a variadic `for`-comprehension, where the generators are the `List[Int]` items in the `List`: the size of the
resullt equals the product of the sizes of each list. (So, just add an empty `List`, of size 0, and the result is empty too).

We slide step with 3, and choose size 2 because of left hand side and right hand side. Then, we shuffle the pairs and `take`
between 2 and 7 items. Finally, we use functions from indices to associate `Op`erators, and create a `List` of `Expr`essions
of type `List[Int]`.
]

Solution
--------

Not in general, no, but for the case of `Set`s, we can interpret `Add`ition as _union_ of sets, `Sub`traction as _difference_
of sets, `Mul`tiplication as _intersection_ of sets, `Div`ision as _symmetric difference_ of sets, and `Inv`ersion as set
_complement_ in rapport to a _universe_:

```Scala
import alleycats.{ Zero, One }

def show[A](xs: Expr[Set[A]])(implicit depth: Int = 0, zero: Zero[Set[A]], one: One[Set[A]], uni: Set[A]): String =
  given Int = depth + 1
  {
    xs match
      case Val(_) | Zero | One => ""
      case _ if depth >= 2     => "( "
      case _                   => ""
  }
  +
  {
    xs match
      case Zero          => if zero.zero.isEmpty then "∅" else zero.zero.toString
      case One           => one.one.mkString("{ ", ", ", " }")
      case Val(set)      => if set.isEmpty then "∅" else set.mkString("{ ", ", ", " }")
      case Inv(rhs)      => "~" + show(rhs)
      case Add(lhs, rhs) => show(lhs) + " ∪ " + show(rhs)
      case Sub(lhs, rhs) => show(lhs) + " ∖ " + show(rhs)
      case Mul(lhs, rhs) => show(lhs) + " ∩ " + show(rhs)
      case Div(lhs, rhs) => show(lhs) + " ∆ " + show(rhs)
  }
  +
  {
    xs match
      case Val(_) | Zero | One => ""
      case _ if depth >= 2     => " )"
      case _                   => ""
  }

implicit def eval[A](xs: Expr[Set[A]])(implicit zero: Zero[Set[A]], one: One[Set[A]], uni: Set[A]): Set[A] =
  xs match
    case Zero          => zero.zero
    case One           => one.one
    case Val(set)      => set
    case Inv(rhs)      => uni &~ rhs
    case Add(lhs, rhs) => lhs ++ rhs
    case Sub(lhs, rhs) => lhs &~ rhs
    case Mul(lhs, rhs) => lhs & rhs
    case Div(lhs, rhs) => (lhs &~ rhs) ++ (rhs &~ lhs)
```

`Expr`ession `for`-comprehensions
---------------------------------

We `import scala.util.control.TailCalls._` and reimplement the `kittensʹExprMonad` typeclass instance of the `Monad` typeclass
for `Expr` by instantiating `StackSafeMonad[Expr]`, and give `flatten` and `map` methods a stack safe definition (although,
more elaborate):

```Scala
import cats.{ Eval, Monad }
import cats.StackSafeMonad

enum Expr[+T]:
  case Add[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case Sub[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case Zero extends Expr[Nothing]
  case Mul[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case Div[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case One extends Expr[Nothing]
  case Inv[+T](rhs: Expr[T]) extends Expr[T]
  case Val[T](n: T) extends Expr[T]

object Expr:
  import scala.util.control.TailCalls._
  implicit val kittensʹExprMonad: Monad[Expr] =
    new StackSafeMonad[Expr]:
      def pure[A](a: A): Expr[A] = Val(a)
      override def flatten[A](fa: Expr[Expr[A]]): Expr[A] =
        def flattenʹ(xa: Expr[Expr[A]]): TailRec[Expr[A]] =
          xa match
            case Val(it)   => done(it)
            case Add(m, n) =>
              for
                mʹ <- tailcall { flattenʹ(m) }
                nʹ <- tailcall { flattenʹ(n) }
              yield
                Add(mʹ, nʹ)
            case Sub(m, n) =>
              for
                mʹ <- tailcall { flattenʹ(m) }
                nʹ <- tailcall { flattenʹ(n) }
              yield
                Sub(mʹ, nʹ)
            case Mul(m, n) =>
              for
                mʹ <- tailcall { flattenʹ(m) }
                nʹ <- tailcall { flattenʹ(n) }
              yield
                Mul(mʹ, nʹ)
            case Div(m, n) =>
              for
                mʹ <- tailcall { flattenʹ(m) }
                nʹ <- tailcall { flattenʹ(n) }
              yield
                Div(mʹ, nʹ)
            case Inv(n)    =>
              for
                nʹ <- tailcall { flattenʹ(n) }
              yield
                Inv(nʹ)
            case it @ (Zero | One) => done(it)
        flattenʹ(fa).result
      override def map[A, B](fa: Expr[A])(f: A => B): Expr[B] =
        def mapʹ(xa: Expr[A]): TailRec[Expr[B]] =
          xa match
            case Val(it)   => done(Val(f(it)))  // line #56
            case Add(m, n) =>
              for
                mʹ <- tailcall { mapʹ(m) }      // line #59
                nʹ <- tailcall { mapʹ(n) }      // line #60
              yield
                Add(mʹ, nʹ)                     // line #62
            case Sub(m, n) =>
              for
                mʹ <- tailcall { mapʹ(m) }
                nʹ <- tailcall { mapʹ(n) }      // line #67
              yield
                Sub(mʹ, nʹ)                     // line #69
            case Mul(m, n) =>
              for
                mʹ <- tailcall { mapʹ(m) }
                nʹ <- tailcall { mapʹ(n) }
              yield
                Mul(mʹ, nʹ)
            case Div(m, n) =>
              for
                mʹ <- tailcall { mapʹ(m) }
                nʹ <- tailcall { mapʹ(n) }
              yield
                Div(mʹ, nʹ)
            case Inv(n)    =>
              for
                nʹ <- tailcall { mapʹ(n) }
              yield
                Inv(nʹ)
            case it @ (Zero | One) => done(it)
        mapʹ(fa).result
      def flatMap[A, B](fa: Expr[A])(f: A => Expr[B]): Expr[B] =
        flatten(map(fa)(f))
      override def tailRecM[A, B](a: A)(f: A => Expr[Either[A, B]]): Expr[B] = // stack safe!
        def tailRecMʹ(a: A): Eval[Expr[B]] =
          def loop(xe: Expr[Either[A, B]]): Eval[Expr[B]] =
            xe match
              case it @ (Zero | One) =>
                Eval.now(it)
              case Val(Left(a)) =>
                for
                  _  <- Eval.Unit
                  xb <- tailRecMʹ(a)
                yield
                  xb
              case Val(Right(b)) =>
                Eval.now(Val(b))
              case Inv(xn) =>
                for
                  n <- loop(xn)
                yield
                  Inv(n)
              case Add(xm, xn) =>
                for
                  m <- loop(xm)
                  n <- loop(xn)
                yield
                  Add(m, n)
              case Sub(xm, xn) =>
                for
                  m <- loop(xm)
                  n <- loop(xn)
                yield
                  Sub(m, n)
              case Mul(xm, xn) =>
                for
                  m <- loop(xm)
                  n <- loop(xn)
                yield
                  Mul(m, n)
              case Div(xm, xn) =>
                for
                  m <- loop(xm)
                  n <- loop(xn)
                yield
                  Div(m, n)
          loop(f(a))
        tailRecMʹ(a).value
```

Let us analyze more closely what happens in `flatten` and `map`; suppose we had the following `for`-comprehension:

```Scala
import cats.syntax.flatMap._, cats.syntax.functor._

val w: Expr[Expr[Int]] =
  for
    x: Int <- Add(Val(1), Val(4)): Expr[Int]  // line #a
    y: Int <- Sub(Zero, Val(5)): Expr[Int]    // line #b
  yield
    Mul(Val(x), Val(y))                       // line #c
```

where all types have been ascribed to variables/expressions (as it turns out, this is necessary for `enum`s which by default
ascribe the `case`'s type rather than the `enum`'s). The `for`-comprehension translates to:

```Scala
(Add(Val(1), Val(4)): Expr[Int]).flatMap { x =>  // line #a
  (Sub(Zero, Val(5)): Expr[Int]).map { y =>      // line #b
    Mul(Val(x), Val(y))                          // line #c
  }
}
```

Now `flatMap` is just `map` followed by `flatten`, se we can rewrite to:

```Scala
(Add(Val(1), Val(4)): Expr[Int]).map { x =>  // line #a
  (Sub(Zero, Val(5)): Expr[Int]).map { y =>  // line #b
    Mul(Val(x), Val(y))                      // line #c
  }
}.flatten                                    // line #d
```

The function-block in line #a, with `x` as parameter, is invoked (line #56) for all cases where there is a `Val` in line #a:
`Val(1)` as left hand side (#line 59), and `Val(4)` as right hand side (line #60) to `Add`. Having `map`ped both sides, `Add`
is used to wrap the results back again (line #62).

On behalf of `Val(1)`, the function-block in line #b, with `y` as parameter, is invoked (line #56) for all cases where there
is a `Val` in line #b: `Val(5)` as right hand side (line #67) to `Sub`. Having `map`ped both sides (the left hand side
_without ever_ invoking `f` in line #56), `Sub` is used to wrap the results back again (line #69).

On behalf of `Val(5)`, line #c evaluates to `Mul(Val(1), Val(5))`, which - wrapped in a `Val` (later removed by `flatten` in
line #d) -, yields `Val(Mul(Val(1), Val(5)))` - the right hand side in line #67. Still on behalf of `Val(1)`, line #69 yields:
`Sub(Zero, Val(Mul(Val(1), Val(5))))`. This is the result in line #59.

Likewise, on behalf of `Val(4)`, the result in line #60 is `Sub(Zero, Val(Mul(Val(4), Val(5))))`; wrapping back in line #62
yields:

```Scala
Add(Val(Sub(Zero, Val(Mul(Val(1), Val(5))))), Val(Sub(Zero, Val(Mul(Val(4), Val(5))))))
```

which `flatten`ed in line #d, gives

```Scala
Add(Sub(Zero, Val(Mul(Val(1), Val(5)))), Sub(Zero, Val(Mul(Val(4), Val(5)))))
```

---

The rationale behind the `map` method is that it operates as if an `Expr`ession was a _collection_ of the same base type, for
the occurrences of _items_ wrapped exclusively in `Val`s: these are the only cases when the function `f: A => B` - parameter
to the method - is applied.

This means that subsequent `Expr`ession generators will be invoked _for each item_; with a slight modification, the following
`for`-comprehension:

```Scala
for
  x: Int <- Add(Div(One, Val(1)), Val(4)): Expr[Int]
  y: Int <- Sub(Val(0), Val(5)): Expr[Int]
yield
  Mul(Val(x), Val(y))
```

behaves like this:

1. on behalf of `Val(1)`:

   - on behalf of `Val(0)`: `Val(Mul(Val(1), Val(0)))`

   - on behalf of `Val(5)`: `Val(Mul(Val(1), Val(5)))`

   - wrapped result: `Sub(Val(Mul(Val(1), Val(0))), Val(Mul(Val(1), Val(5))))`

1. wrapped result: `Div(One, Val(Sub(Val(Mul(Val(1), Val(0))), Val(Mul(Val(1), Val(5))))))`

1. on behalf of `Val(4)`:

   - on behalf of `Val(0)`: `Val(Mul(Val(4), Val(0)))`

   - on behalf of `Val(5)`: `Val(Mul(Val(4), Val(5)))`

   - wrapped result: `Sub(Val(Mul(Val(4), Val(0))), Val(Mul(Val(4), Val(5))))`

1. wrapped result: `Val(Sub(Val(Mul(Val(4), Val(0))), Val(Mul(Val(4), Val(5)))))`

1. end wrapped result:

```Scala
Add(Div(One, Val(Sub(Val(Mul(Val(1), Val(0))), Val(Mul(Val(1), Val(5))))))
   ,Val(Sub(Val(Mul(Val(4), Val(0))), Val(Mul(Val(4), Val(5))))))
```

6. which `flatten`ed gives:

```Scala
Add(Div(One, Sub(Val(Mul(Val(1), Val(0))), Val(Mul(Val(1), Val(5)))))
   ,Sub(Val(Mul(Val(4), Val(0))), Val(Mul(Val(4), Val(5)))))
```

The comparison with collections consisted in the following `for`-comprehension:

```Scala
for
  x <- List(1, 4)
  y <- List(0, 5)
yield
  Mul(Val(x), Val(y))
```

which yields:

```Scala
List(Mul(Val(1), Val(0)), Mul(Val(1), Val(5)), Mul(Val(4), Val(0)), Mul(Val(4), Val(0)))
```

The combinatorics is the same. The only difference is that, while finding and `map`ping _items_ from sub-`Expr`essions,
unwrapping and wrapping takes place. On either the left hand side or the right hand side, it is possible that _no_ `map`ping
occurs (there are no terminal `Val`s): these appear identical back in the result.

The invariant maintained is that the `Expr`essions are always correct, although generated in all possible ways; this may
sound a bit tricky: there is only one parameter to `Val`, how can we put "more" `Expr`essions instead?! A `for`-comprehension
acts in opposition: a combination of parameters to `Val`, one for each generator, is current at any given yielding: these are
substituted in the resulting expression. Now, starting with the last generator, for two succesive `Val`s the resulting
expressions make up the left hand side and the right hand side of an operator (`Add`, `Sub`, `Mul`, `Div`, or `Inv`).

When _all_ the `Val`s in the last generator have been `map`ped, corresponding owning `Expr`essions are reconstructed by
wrapping back: there is _exactly one_ result for the current `Val` in the penultimate generator.

In other words, although there are _many_ resulting `Expr`essions from the next generator, each `map`s from the argument in
_exactly one_ `Val` in the previous generator. In this way, a `for`-comprehension acts much like a perfectly balanced tree:
for each node in the previous level (previous generator) there are distinct _trees_ on the next level (next generator). Note
that in the following illustration, `Val(n)`s are omitted, only `n`s are shown instead.

```
                      for                                                            ___ for ___
                      / \                                                           /           \
               ______/   \______                       Add(Div(One, Sub(Mul(1, 0), Mul(1, 5))), Sub(Mul(4, 0), Mul(4, 5)))
              /                 \                                     /                                   \
             /                   \                                   /                                     \
            /                     \                                 /                                       \
           1                       4                Div(One, Sub(Mul(1, 0), Mul(1, 5)))         Val(Sub(Mul(4, 0), Mul(4, 5)))
          / \                     / \                                |                                         |
         /   \                   /   \                               |                                         |
        0     5                 0     5                  Sub(Mul(1, 0), Mul(1, 5))                Sub(Mul(4, 0), Mul(4, 5))
       /       \               /       \                /                         \              /                         \
      /         \             /         \              /                           \            /                           \
Mul(1, 0)   Mul(1, 5)   Mul(4, 0)   Mul(4, 5)     Mul(1, 0)                    Mul(1, 5)   Mul(4, 0)                    Mul(4, 5)
```

Solution (cont'd)
-----------------

We use two lists of lists wherefrom to generate sets. After we convert sub-lists of them into lists of `Expr`essions of type
`List[Int]`, we concatenate them in just one `List`, which we `traverse` with `kittensʹExprMonad: Monad[Expr]`:

```Scala
val xs1 = opsify(List(List(1,2,3),List(2,3,4),List(0,4,5)))
val xs2 = opsify(List(List(1,0,4),List(2,-1,5),List(0,2,3)))

val xs3: Expr[List[Set[Int]]] = (xs1 ++ xs2)
  .traverse(identity)
  .map(_.map(_.toSet))
```

`traverse`ing with an `Expr`ession
----------------------------------

As instance of `StackSafemonad`, when `(xs1 ++ xs2): List[Expr[Set[Int]]]` is `traverse`d (with `identity`), it matches the
[case](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md#traverselist) when a `Traverse.traverseDirectly`
is invoked, which `foldLeft`s the `List`'s iterator, using `G.map2` (where `G: Applicative[G]` is used for traversal), in our
case, `kittensʹExprMonad.map2`, which inherits this method from `FlatMap`, whose definition is:

```Scala
package cats

trait FlatMap[F[_]] extends ... {
  override def map2[A, B, Z](fa: F[A], fb: F[B])(f: (A, B) => Z): F[Z] =
    flatMap(fa)(a => map(fb)(f(a, _)))}
```

and can be rewritten as:

```Scala
package cats

trait FlatMap[F[_]] extends ... {
  override def map2[A, B, Z](fa: F[A], fb: F[B])(f: (A, B) => Z): F[Z] =
    map(fa) {        // line #a
      a =>
        map(fb) {    // line #b
          b =>
            f(a, b)  // line #c
        }
    }.flatten        // line #d
}
```

or even - why not - as a `for`-comprehension:

```Scala
package cats

trait FlatMap[F[_]] extends ... {
  override def map2[A, B, Z](fa: F[A], fb: F[B])(f: (A, B) => Z): F[Z] =
    { for
        a <- fa  // line #a
        b <- fb  // line #b
      yield
        f(a, b)  // line #c
    }.flatten    // line #d
}
```

Although a typeclass instance of the `Monad` typeclass, an `Expr`ession behaves much like a pseudo-collection.

There are two _different_ things to notice:

1. one thing is the return value from `map`;

1. another thing is applying the `map` function on the pseudo-items.

We can make an observation in each case:

1. an `Expr`ession has a dynamic part (`Val`), but unlike `Option`, an `Expr`ession generally has a complex _structure_ that
   is _constant_: both `fa` from line #a and `fb` from line #b _keep_ their structure upon the return from `map`;

1. the pseudo-item as _operand_, can be either a left hand side or a _right hand side_ - in our case, the latter.

Another thing to notice is that, while the `b`s ranged over by line #b vary, the `a` from line #a _does not_. Also, note that
when `a` varies, the `b`s - ranged overy by line #b - vary unconditionally in _the same_ way: the dependency on `a` is the
same. The only thing that changes with `a` or `b` is what arguments are passed to `f`.

---

Initially, `fa` equals `Val(Chain())`: an empty `Chain` lifted into `Expr`. Now, if `fb` had several `Val`s (say three,
`Val(k)`, `Val(m)`, `Val(n)`), - where `k`, `m`, `n` were lists - there would be three `append`ings (yes, applications of the
function `f`): `Chain() :+ k`, `Chain() :+ m`, `Chain() :+ n`, resulting in the singletons, respectively, `Chain(k)`,
`Chain(m)`, `Chain(n)`. With these latter three instead of the former, `fbʹ` (`fb` _prime_) will otherwise keep the
structure of `fb` - the return value from block #b.

Because this occurred on behalf of applying the function in line #b on `a`, `Chain()` will be substituted with `fbʹ`,
resulting in `Val(fbʹ)`, which `flatten`ed yields `fbʹ: Expr[Chain[List[Int]]]` - the return of `map2`, used as the _next_
accumulator in the `foldLeft` traversal.

Next, assume `fa` equals `fbʹ`: this time, `fa` might have `Val`s more and deeper than just a surface one; in our example,
three: `Val(Chain(k))`, `Val(Chain(m))`, `Val(Chain(n))`. If `fb` had several `Val`s (say two, `Val(p)`, `Val(q)`), - where
`p`, `q` were lists - there would be _six_ `append`ings (yes, applications of the function `f`):

1. fixing `k` in `fa`, varying with `p` and `q` in `fb`, there will result an `Expr`ession denoted by `fbʹʹkpq`;

1. fixing `m` in `fa`, varying with `p` and `q` in `fb`, there will result an `Expr`ession denoted by `fbʹʹmpq`;

1. fixing `n` in `fa`, varying with `p` and `q` in `fb`, there will result an `Expr`ession denoted by `fbʹʹnpq`.

By the second generator from line #b, the `Expr`essions `fbʹʹkpq`, `fbʹʹmpq`, and `fbʹʹnpq` have the same constant part as
`fb`, except that:

1. `fbʹʹkpq` will have substituted `Chain(k, p)` for `p` and `Chain(k, q)` for `q` in `fb`;

1. `fbʹʹmpq` will have substituted `Chain(m, p)` for `p` and `Chain(m, q)` for `q` in `fb`;

1. `fbʹʹnpq` will have substituted `Chain(n, p)` for `p` and `Chain(n, q)` for `q` in `fb`.

By the first generator from line #a:

1. `fbʹʹkpq` substitutes `Chain(k)`;

1. `fbʹʹmpq` substitutes `Chain(m)`;

1. `fbʹʹnpq` substitutes `Chain(n)`.

Finally, line #d will `flatten` the occurrences wrapped in `Val` - `Val(fbʹʹkpq)`, `Val(fbʹʹkpq)`, `Val(fbʹʹkpq)` -, into,
respectively, `fbʹʹkpq`, `fbʹʹkpq`, `fbʹʹkpq`. And so on, and so forth.

Solution (cont'd)
-----------------

In order to obtain an `Expr[Set[Int]]`, we use the method `map` of `Expr` to `shuffle` each `List[Set[Int]]`, take between 2
and 7 sets, and reduce them via intersection (`&`) operator:

```Scala
val xs: Expr[Set[Int]] = xs3.map {
  shuffle(_)
    .take(2+nextInt(5))
    .reduce(_ & _)
}
```

Finally, we use the empty set - as `Zero`, a set derived from a number with both the negative and the positive - as `One`,
and a universe with numbers from -5 to 5; we `evaluate` our `Expr`essions in `Set` and `show` the end result:

```Scala
{
  implicit val zero: Zero[Set[Int]] = Zero(Set.empty)
  implicit def one(implicit n: Int): One[Set[Int]] = One(Set(-n, n))
  implicit val universe: Set[Int] = Set.from(-5 to 5)

  given Int = 1

  println(show(xs))

  println(show(Val(eval(xs))))
}
```

[First](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/traverse-4-nel/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/traverse-6-list/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md)
