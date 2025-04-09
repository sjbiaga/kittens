[Previous](https://github.com/sjbiaga/kittens/blob/main/eval-1-function0/README.md)

Lesson 06: Natural Transformations (cont'd)
===========================================

Exercise 06.6
-------------

First, implement a typeclass instance `kittensExprMonad` of the `Monad` typeclass for `Expr`; second, given the `fibonacci`
and `factorial` algorithms implementation for the `Free` monad with `Expr` as the suspension functor:

```Scala
import cats.Free
import Free._

case class Algorithms(n: Int):
  private def fibonacci(k: Int): Free[Expr, Expr[Int]] =
    if k < 2
    then
      liftF { if k < 1 then Zero else One }
    else
      for
        m <- defer { fibonacci(k - 2) }
        n <- defer { fibonacci(k - 1) }
      yield
        Add(m, n)
  private def factorial(k: Int): Free[Expr, Expr[Int]] =
    if k < 1
    then
      liftF { One }
    else
      for
        n <- defer { factorial(k - 1) }
      yield
        Mul(Val(k), n)
  def fib: Free[Expr, Expr[Int]] = fibonacci(n)
  def fac: Free[Expr, Expr[Int]] = factorial(n)
```

use a natural transformation `treeify` (see
[Exercise 06.3](https://github.com/sjbiaga/kittens/blob/main/expr-tree/README.md)) to modify the suspension functor from
`Expr` to `Tree`:

```Scala
enum Op:
  case Add, Sub, Mul, Div, Inv
enum Tree[+T]:
  val result: T
  case Leaf[+T](override val result: T) extends Tree[T]
  case Node[+T](override val result: T,
                operator: Op,
                left: Option[Tree[T]],
                right: Option[Tree[T]]) extends Tree[T]
```

and actually use a typeclass instance `kittensTreeMonad` of the `Monad` typeclass for `Tree` to perform the computation.

Third, implement `Algorithmsʹ` to directly return `Free[Tree, Expr[Int]]` and run using the `kittensTreeMonad`. Evaluate the
result in a `DivisionRing[Int]`: should it be used directly or implicitly?

Solution - Part 1
-----------------

The typeclass instance of the `Monad` typeclass for `Expr` is _not_ stack safe: the implementation of the `tailRecM` method
cannot be annotated `@tailrec`. The `flatMap` method is defined in terms of `flatten` and `map`. Both are recursive
algorithms, with just one interesting _base_ case: `Val`. The former deflates from `Val(it: Expr[A]): Expr[Expr[A]]` to
`it`. The latter - in the case when it is being called from `flatMap` - inflates using the function `f: A => Expr[B]` from
`Val(it: A)` to `Val(f(it)): Expr[Expr[B]]`. The _recursive_ cases just _unwrap_ the (two) operand(s) - call either `flatten`
or `map` - and then _wrap_ the result(s) back:

```Scala
import cats.Monad

implicit val kittensExprMonad: Monad[Expr] =
  new Monad[Expr]:
    def pure[A](a: A): Expr[A] = Val(a)
    override def flatten[A](fa: Expr[Expr[A]]): Expr[A] =
      fa match
        case Val(it)   => it
        case Add(n, m) => Add(flatten(n), flatten(m))
        case Sub(n, m) => Sub(flatten(n), flatten(m))
        case Mul(n, m) => Mul(flatten(n), flatten(m))
        case Div(n, m) => Div(flatten(n), flatten(m))
        case Inv(n)    => Inv(flatten(n))
        case it @ (Zero | One ) => it
    override def map[A, B](fa: Expr[A])(f: A => B): Expr[B] =
      fa match
        case Val(it)   => Val(f(it))
        case Add(n, m) => Add(map(n)(f), map(m)(f))
        case Sub(n, m) => Sub(map(n)(f), map(m)(f))
        case Mul(n, m) => Mul(map(n)(f), map(m)(f))
        case Div(n, m) => Div(map(n)(f), map(m)(f))
        case Inv(n)    => Inv(map(n)(f))
        case it @ (Zero | One ) => it
    def flatMap[A, B](fa: Expr[A])(f: A => Expr[B]): Expr[B] = flatten(map(fa)(f))
    def tailRecM[A, B](a: A)(f: A => Expr[Either[A, B]]): Expr[B] =
      flatMap(f(a))(_.fold(tailRecM(_)(f), pure))
```

Solution - Part 2
-----------------

We can derive `Node`s or `Leaf`s easily from an `Expr`ession, by cases, but the `result` field of the `Tree`s must be
`eval`uated beforehand: we do this latter in a `DivisionRing`:

```Scala
import algebra.ring._

implicit def eval[A](expr: Expr[A])(implicit R: DivisionRing[A]): A =
  expr match
    case Zero      => R.zero
    case One       => R.one
    case Val(v)    => v
    case Inv(n)    => R.negate(n)
    case Add(m, n) => R.plus(m, n)
    case Mul(m, n) => R.times(m, n)
    case Sub(m, n) => R.minus(m, n)
    case Div(m, n) => R.div(m, n)
```

The `treeify` natural transformation should use an implicit `DivisionRing`, but it gets ugly because we cannot pass it
directly to the `apply[A]` method of `FunctionK`; so, we must pass it with wildcard to the `treeify` method first and coerce
it to `DivisionRing[A]` second:

```Scala
import cats.arrow.FunctionK

def treeify(R: DivisionRing[?]): FunctionK[Expr, Tree] =
  new FunctionK[Expr, Tree]:
    def apply[A](xa: Expr[A]): Tree[A] =
      implicit val Rʹ: DivisionRing[A] = R.asInstanceOf[DivisionRing[A]]
      xa match
        case Inv(n)    => Node(eval(xa), Op.Inv, None, Some(apply(n)))
        case Add(m, n) => Node(eval(xa), Op.Add, Some(apply(m)), Some(apply(n)))
        case Mul(m, n) => Node(eval(xa), Op.Mul, Some(apply(m)), Some(apply(n)))
        case Sub(m, n) => Node(eval(xa), Op.Sub, Some(apply(m)), Some(apply(n)))
        case Div(m, n) => Node(eval(xa), Op.Div, Some(apply(m)), Some(apply(n)))
        case _         => Leaf(eval(xa))
```

The typeclass instance of the `Monad` typeclass for `Tree` is _not_ stack safe either. The `flatMap` method is defined in
terms of `flatten` and `map`, again. But only `map` is a recursive algorithm, whereas `flatten` is straight the `result`
field from any `Tree`:

```Scala
implicit val kittensTreeMonad: Monad[Tree] =
  new Monad[Tree]:
    def pure[A](a: A): Tree[A] = Leaf(a)
    override def flatten[A](fa: Tree[Tree[A]]): Tree[A] = fa.result
    override def map[A, B](fa: Tree[A])(f: A => B): Tree[B] =
      fa match
        case Leaf(a)                           => Leaf(f(a))
        case Node(a, Op.Inv, _,       Some(n)) => Node(f(a), Op.Inv, None,            Some(map(n)(f)))
        case Node(a, Op.Add, Some(m), Some(n)) => Node(f(a), Op.Add, Some(map(m)(f)), Some(map(n)(f)))
        case Node(a, Op.Sub, Some(m), Some(n)) => Node(f(a), Op.Sub, Some(map(m)(f)), Some(map(n)(f)))
        case Node(a, Op.Mul, Some(m), Some(n)) => Node(f(a), Op.Mul, Some(map(m)(f)), Some(map(n)(f)))
        case Node(a, Op.Div, Some(m), Some(n)) => Node(f(a), Op.Div, Some(map(m)(f)), Some(map(n)(f)))
    def flatMap[A, B](fa: Tree[A])(f: A => Tree[B]): Tree[B] = flatten(map(fa)(f))
    def tailRecM[A, B](a: A)(f: A => Tree[Either[A, B]]): Tree[B] =
      flatMap(f(a))(_.fold(tailRecM(_)(f), pure))
```

Before the actual computation, we must make implicits the `DivisionRing`s which we use (perhaps implicitly, later):

```Scala
implicit val kittensIntRing: DivisionRing[Int] =
  new DivisionRing[Int]:
    override val zero = 0d
    override val one = 1d
    override def negate(n: Int) = 0d - n
    override def reciprocal(n: Int) = ???
    override def plus(m: Int, n: Int) = m + n
    override def minus(m: Int, n: Int) = m - n
    override def times(m: Int, n: Int) = m * n
    override def div(m: Int, n: Int) = m / n

implicit def kittensExprRing[A]: DivisionRing[Expr[A]] =
  new DivisionRing[Expr[A]]:
    override val zero = Zero
    override val one = One
    override def negate(n: Expr[A]) = Inv(n)
    override def reciprocal(n: Expr[A]) = ???
    override def plus(m: Expr[A], n: Expr[A]) = Add(m, n)
    override def minus(m: Expr[A], n: Expr[A]) = Sub(m, n)
    override def times(m: Expr[A], n: Expr[A]) = Mul(m, n)
    override def div(m: Expr[A], n: Expr[A]) = Div(m, n)
```

We may now use the `mapK` method in the `Free` monad to modify the suspension functor from `Expr` to `Tree`, then run it to
completion:

```scala
scala> val as = Algorithms(10)

scala> as.fib.mapK(treeify(kittensExprRing))
val res0: cats.free.Free[Tree, Expr[Int]] = Free(...)

scala> res0.runTailRec
val res1: Tree[Expr[Int]] = Leaf(Add(Add(Add(Add(Add(Zero,One),Add(One,Add(Zero,One))),Add(Add(One,Add(Zero,One)),Add(Add(Zero,One),Add(One,Add(Zero,One))))),Add(Add(Add(One,Add(Zero,One)),Add(Add(Zero,One),Add(One,Add(Zero,One)))),Add(Add(Add(Zero,One),Add(One,Add(Zero,One))),Add(Add(One,Add(Zero,One)),Add(Add(Zero,One),Add(One,Add(Zero,One))))))),Add(Add(Add(Add(One,Add(Zero,One)),Add(Add(Zero,One),Add(One,Add(Zero,One)))),Add(Add(Add(Zero,One),Add(One,Add(Zero,One))),Add(Add(One,Add(Zero,One)),Add(Add(Zero,One),Add(One,Add(Zero,One)))))),Add(Add(Add(Add(Zero,One),Add(One,Add(Zero,One))),Add(Add(One,Add(Zero,One)),Add(Add(Zero,One),Add(One,Add(Zero,One))))),Add(Add(Add(One,Add(Zero,One)),Add(Add(Zero,One),Add(One,Add(Zero,One)))),Add(Add(Add(Zero,One),Add(One,Add(Zero,One))),Add(Add(One,Add(Zero,One)),Add(Add(Zero,One),Add(One,Add(Zero,One))))))))))

scala> kittensTreeMonad.map(res1)(eval)
val res2: Tree[Int] = Leaf(55)

scala> res2.result
val res3: Int = 55
```

The value `res1` contains a "listing" of the computation of fibonacci: we may see that the _same_ computation repeats many
times, e.g., `Add(One,Add(Zero,One))`; if these were real numbers and arithmetic operators, the `Expr`ession shows precisely
how they are computed, i.e., `1 + (0 + 1)`.

Note that `runTailRec` expects an implicit `Monad[Tree]` which is `kittensTreeMonad`, through which we are also able to
evaluate the `Expr`ession as the `res3` `Int`eger.

Solution - Part 3
-----------------

Because the type of `Tree` is `Expr[Int]` (and not `Int`), the `result` fields in `Leaf`s and `Node`s are `Expr`essions
(rather than `Int`egers):

```Scala
case class Algorithmsʹ(n: Int):
  private def fibonacci(k: Int): Free[Tree, Tree[Expr[Int]]] =
    if k < 2
    then
      liftF { Leaf(Leaf(if k < 1 then Zero else One)) }
    else
      for
        m <- defer { fibonacci(k - 2) }
        n <- defer { fibonacci(k - 1) }
      yield
        Node(Add(m.result, n.result), Op.Add, Some(m), Some(n))
  private def factorial(k: Int): Free[Tree, Tree[Expr[Int]]] =
    if k < 1
    then
      liftF { Leaf(Leaf(One)) }
    else
      for
        n <- defer { factorial(k - 1) }
      yield
        Node(Mul(Val(k), n.result), Op.Mul, Some(Leaf(Val(k))), Some(n))
  def fib: Free[Tree, Tree[Expr[Int]]] = fibonacci(n)
  def fac: Free[Tree, Tree[Expr[Int]]] = factorial(n)
```

Notice how `Add(m.result, n.result)` and `Mul(Val(k), n.result)` are similar in a way with their counterparts in `Algorithms`.
We instantiate `Algorithmsʹ` and run `fac`torial to completion; again, computations will be repeated:

```scala
scala> val asʹ = Algorithmsʹ(10)
val asʹ: Algorithmsʹ = Algorithmsʹ(10)

scala> asʹ.fac.runTailRec
val res4: Tree[Tree[Expr[Int]]] = Leaf(Node(Mul(Val(10),Mul(Val(9),Mul(Val(8),Mul(Val(7),Mul(Val(6),Mul(Val(5),Mul(Val(4),Mul(Val(3),Mul(Val(2),Mul(Val(1),One)))))))))),Mul,Some(Leaf(Val(10))),Some(Node(Mul(Val(9),Mul(Val(8),Mul(Val(7),Mul(Val(6),Mul(Val(5),Mul(Val(4),Mul(Val(3),Mul(Val(2),Mul(Val(1),One))))))))),Mul,Some(Leaf(Val(9))),Some(Node(Mul(Val(8),Mul(Val(7),Mul(Val(6),Mul(Val(5),Mul(Val(4),Mul(Val(3),Mul(Val(2),Mul(Val(1),One)))))))),Mul,Some(Leaf(Val(8))),Some(Node(Mul(Val(7),Mul(Val(6),Mul(Val(5),Mul(Val(4),Mul(Val(3),Mul(Val(2),Mul(Val(1),One))))))),Mul,Some(Leaf(Val(7))),Some(Node(Mul(Val(6),Mul(Val(5),Mul(Val(4),Mul(Val(3),Mul(Val(2),Mul(Val(1),One)))))),Mul,Some(Leaf(Val(6))),Some(Node(Mul(Val(5),Mul(Val(4),Mul(Val(3),Mul(Val(2),Mul(Val(1),One))))),Mul,Some(Leaf(Val(5))),Some(Node(Mul(Val(4),Mul(Val(3),Mul(Val(2),Mul(Val(1),One)))),Mul,Some(Leaf(Val(4))),Some(Node(Mul(Val(3),Mul(Val(2),Mul(Val(1),One))),Mul,Some(Leaf(Val(3))),Some(Node(Mul(Val(2),Mul(Val(1),One)),Mul,Some(Leaf(Val(2))),Some(Node(Mul(Val(1),One),Mul,Some(Leaf(Val(1))),Some(Leaf(One))))))))))))))))))))))
```

We should be able to `eval`uate the `Expr`essions in all the `Node`s of the tree; the root contains the actual final `result`:

```scala
scala> kittensTreeMonad.flatten(res4)
val res5: Tree[Expr[Int]] = Node(Mul(Val(10),Mul(Val(9),Mul(Val(8),Mul(Val(7),Mul(Val(6),Mul(Val(5),Mul(Val(4),Mul(Val(3),Mul(Val(2),Mul(Val(1),One)))))))))),Mul,Some(Leaf(Val(10))),Some(Node(Mul(Val(9),Mul(Val(8),Mul(Val(7),Mul(Val(6),Mul(Val(5),Mul(Val(4),Mul(Val(3),Mul(Val(2),Mul(Val(1),One))))))))),Mul,Some(Leaf(Val(9))),Some(Node(Mul(Val(8),Mul(Val(7),Mul(Val(6),Mul(Val(5),Mul(Val(4),Mul(Val(3),Mul(Val(2),Mul(Val(1),One)))))))),Mul,Some(Leaf(Val(8))),Some(Node(Mul(Val(7),Mul(Val(6),Mul(Val(5),Mul(Val(4),Mul(Val(3),Mul(Val(2),Mul(Val(1),One))))))),Mul,Some(Leaf(Val(7))),Some(Node(Mul(Val(6),Mul(Val(5),Mul(Val(4),Mul(Val(3),Mul(Val(2),Mul(Val(1),One)))))),Mul,Some(Leaf(Val(6))),Some(Node(Mul(Val(5),Mul(Val(4),Mul(Val(3),Mul(Val(2),Mul(Val(1),One))))),Mul,Some(Leaf(Val(5))),Some(Node(Mul(Val(4),Mul(Val(3),Mul(Val(2),Mul(Val(1),One)))),Mul,Some(Leaf(Val(4))),Some(Node(Mul(Val(3),Mul(Val(2),Mul(Val(1),One))),Mul,Some(Leaf(Val(3))),Some(Node(Mul(Val(2),Mul(Val(1),One)),Mul,Some(Leaf(Val(2))),Some(Node(Mul(Val(1),One),Mul,Some(Leaf(Val(1))),Some(Leaf(One)))))))))))))))))))))

scala> kittensTreeMonad.map(res5)(eval)
val res6: Tree[Int] = Node(3628800,Mul,Some(Leaf(10)),Some(Node(362880,Mul,Some(Leaf(9)),Some(Node(40320,Mul,Some(Leaf(8)),Some(Node(5040,Mul,Some(Leaf(7)),Some(Node(720,Mul,Some(Leaf(6)),Some(Node(120,Mul,Some(Leaf(5)),Some(Node(24,Mul,Some(Leaf(4)),Some(Node(6,Mul,Some(Leaf(3)),Some(Node(2,Mul,Some(Leaf(2)),Some(Node(1,Mul,Some(Leaf(1)),Some(Leaf(1)))))))))))))))))))))

scala> res6.result
val res7: Int = 3628800
```

Because the type of the tree in `res5` is `Expr[Int]`, when for the computation of `res6` we use `eval`, the implicit
`DivisionRing[Int]` is `kittensIntRing` - so, it is used _implicitly_, not directly.

[Previous](https://github.com/sjbiaga/kittens/blob/main/eval-1-function0/README.md)
