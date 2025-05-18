[First](https://github.com/sjbiaga/kittens/blob/main/recursion-1-lambda-calculus/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/recursion-1-lambda-calculus/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/recursion-3-Cofree/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/recursion-4-Defer/README.md)

Lesson 09 - Recursion (cont'd)
==============================

The [`fix` Combinator](https://free.cofree.io/2017/08/28/fixpoint) in Scala
---------------------------------------------------------------------------

If we were to define the `fib`onacci recursive algorithm, we would be obliged to use `fib` itself in the body of this very
function:

```Scala
val fib: Long => Long = { n =>
  if n <= 1L
  then
    1L min (0L max n)
  else
    fib(n-1) + fib(n-2)
}
```

We would like - as illustrated before - to define a `fibF: Long => Long` function that does _not_ invoke itself recursively;
for this, we have to translate the `Y` combinator in `Scala`, as
[pointed out](https://free.cofree.io/2017/08/28/fixpoint#factorial-via-fix):

```Scala
def fix[A](f: (=> A) => A): A = {
  lazy val loop: A = f(loop)
  loop
}
```

```Scala
val fibF = fix[Long => Long] { fib =>
  { n =>
    if n <= 1L
    then
      1L min (0L max n)
    else
      fib(n-1) + fib(n-2)
  }
}
```

[Recursion Schemes in Scala](https://free.cofree.io/2017/11/13/recursion)
-------------------------------------------------------------------------

As [pointed out](https://free.cofree.io/2017/11/13/recursion#fixpoint-type), the _fixpoint type_ works exactly as the `Y`
combinator, only at the type level:

```Scala
final case class Fix[F[_]](unfix: F[Fix[F]])
```

As [pointed out](https://jtobin.io/practical-recursion-schemes#a-short-digression-on-fix), `Fix` adds a level of recursion,
while `unfix` removes one level of recursion.

We use the language of expressions from [Lesson 03](https://github.com/sjbiaga/kittens/blob/main/expr-01-trait/README.md):

```Scala
sealed trait ExprF[+R]
case class AddF[+R](lhs: R, rhs: R) extends ExprF[R]
case class SubF[+R](lhs: R, rhs: R) extends ExprF[R]
case object ZeroF extends ExprF[Nothing]
case class MulF[+R](lhs: R, rhs: R) extends ExprF[R]
case class DivF[+R](lhs: R, rhs: R) extends ExprF[R]
case object OneF extends ExprF[Nothing]
case class InvF[+R](rhs: R) extends ExprF[R]
case class ValF[T](n: T) extends ExprF[Nothing]
case class FacF[+R, T](n: R, k: T) extends ExprF[R]
```

with a slight alteration: type parameter `R` stands for "_R_ecursion". We let type parameter `T` be the non-recursive type
(for `ValF` and `FacF` only).

To use recursion schemes, `ExprF` must be a `Functor`:

```Scala
import cats.Functor

object ExprF:
  implicit def kittensExprFunctor: Functor[ExprF] =
     new Functor[ExprF]:
       override def map[A, B](xa: ExprF[A])(f: A => B): ExprF[B] =
         xa match
           case AddF(lhs, rhs) => AddF(f(lhs), f(rhs))
           case SubF(lhs, rhs) => SubF(f(lhs), f(rhs))
           case MulF(lhs, rhs) => MulF(f(lhs), f(rhs))
           case DivF(lhs, rhs) => DivF(f(lhs), f(rhs))
           case InvF(rhs)      => InvF(f(rhs))
           case FacF(n, k)     => FacF(f(n), k)
           case it @ (ValF(_) | ZeroF | OneF) => it
```

If we refer to instances of `ExprF` as terms, then an [_algebra_](https://en.wikipedia.org/wiki/Algebraic_structure) is an
_interpretation_ of terms (with a carrier, e.g., `Long` or `Set`, and operations defined on it), whereas a
[_coalgebra_](https://en.wikipedia.org/wiki/Coalgebra) is a _generation_ of terms, e.g, a corecursive algorithm.

The `eval`uation in this sense is an algebra:

```Scala
def eval(xa: ExprF[Long]): Long =
  xa match
    case AddF(lhs, rhs)   => lhs + rhs
    case SubF(lhs, rhs)   => lhs - rhs
    case MulF(lhs, rhs)   => lhs * rhs
    case DivF(lhs, rhs)   => lhs / rhs
    case InvF(rhs)        => 0 - rhs
    case ValF(n: Long)    => n
    case FacF(n, k: Long) => n * k
    case ZeroF            => 0
    case OneF             => 1
```

For a coalgebra, we can define the `factorial` corecursive algorithm - which we could not have without `FactF` (although it
is possible to use a "coproduct" `type ExprFacF[R] = Either[ExprF[R], FacF[R, Long]]`, see [Exercise 09.1](#exercise-091)):

```Scala
def factorial(n: Long): ExprF[Long] =
  if n <= 0
  then
    OneF
  else
    FacF(n-1, n)
```

or the `fibonacci` corecursive algorithm:

```Scala
def fibonacci(n: Long): ExprF[Long] =
  if n == 0
  then
    ZeroF
  else if n == 1
  then
    OneF
  else
    AddF(n-1, n-2)
```

The dictionary entry for `Ana` is:

     A prefix in words from the Greek, denoting up, upward.

```Scala
def ana[F[_]: Functor, A](f: A => F[A]): A => Fix[F] =
  a => Fix(f(a) map ana(f))
```

The dictionary entry for `Cata` is:

     The Latin and English form of a Greek preposition, used as a prefix to signify down, downward.

```Scala
def cata[F[_]: Functor, A](f: F[A] => A): Fix[F] => A =
  fix => f(fix.unfix map cata(f))
```

Exercise 09.1
-------------

Using _separate_ types for, respectively, `Expr`essions, and `FacF` for the special case of the `factorial` algorithm:

```Scala
case class FacF[+R, T](n: R, k: T)
```

define the type (together with its typeclass instance of the `Functor` typeclass):

```Scala
type ExprFacF[R] = Either[ExprF[R], FacF[R, Long]]
```

and the coproduct `:+:` operator on algebras:

```Scala
extension [F[_], A](alg: F[A] => A)
  infix def :+:[G[_]](algʹ: G[A] => A): Either[F[A], G[A]] => A =
    _.fold(alg, algʹ)
```

then implement the `factorial` corecursive algorithm in terms of `ExprFacF`, while using the coproduct of the respective
algebras (one for `ExprF[Long]` and one for `FacF[Long, Long]`) to execute it.

Solution
--------

`Expr`essions are defined as follows, together with the typeclass instance of the `Functor` typeclass, and with the `eval`uate
algebra:

```Scala
sealed trait ExprF[+R]
case class AddF[+R](lhs: R, rhs: R) extends ExprF[R]
case class SubF[+R](lhs: R, rhs: R) extends ExprF[R]
case object ZeroF extends ExprF[Nothing]
case class MulF[+R](lhs: R, rhs: R) extends ExprF[R]
case class DivF[+R](lhs: R, rhs: R) extends ExprF[R]
case object OneF extends ExprF[Nothing]
case class InvF[+R](rhs: R) extends ExprF[R]
case class ValF[T](n: T) extends ExprF[Nothing]

object ExprF:
  implicit val kittensExprFunctor: Functor[ExprF] =
     new Functor[ExprF]:
       override def map[A, B](xa: ExprF[A])(f: A => B): ExprF[B] =
         xa match
           case AddF(lhs, rhs) => AddF(f(lhs), f(rhs))
           case SubF(lhs, rhs) => SubF(f(lhs), f(rhs))
           case MulF(lhs, rhs) => MulF(f(lhs), f(rhs))
           case DivF(lhs, rhs) => DivF(f(lhs), f(rhs))
           case InvF(rhs)      => InvF(f(rhs))
           case it @ (ValF(_) | ZeroF | OneF) => it

  def eval(xa: ExprF[Long]): Long =
    xa match
      case AddF(lhs, rhs)   => lhs + rhs
      case SubF(lhs, rhs)   => lhs - rhs
      case MulF(lhs, rhs)   => lhs * rhs
      case DivF(lhs, rhs)   => lhs / rhs
      case InvF(rhs)        => 0 - rhs
      case ValF(n: Long)    => n
      case ZeroF            => 0
      case OneF             => 1
```

We have eliminated `FacF`, which now is just a `case class`, together with the typeclass instance of the `Functor` typeclass,
and with the `eval`uate (prime) algebra:

```Scala
case class FacF[+R, T](n: R, k: T)

object FacF:
  implicit def kittensFacFunctor[T]: Functor[[R] =>> FacF[R, T]] =
     new Functor[[R] =>> FacF[R, T]]:
       override def map[A, B](fa: FacF[A, T])(f: A => B): FacF[B, T] =
         fa match
           case FacF(n, k) => FacF(f(n), k)

  def evalʹ(fa: FacF[Long, Long]): Long =
    fa match
      case FacF(n, k) => n * k
```

The coproduct algebra is `eval :+: evalʹ`. To match it, for the `factorial` algorithm we need to combine `ExprF` and `FacF`:

```Scala
type ExprFacF[R] = Either[ExprF[R], FacF[R, Long]]

object ExprFacF:
  implicit val kittensExprFacFunctor: Functor[ExprFacF] =
    new Functor[ExprFacF]:
      override def map[A, B](ea: ExprFacF[A])(f: A => B): ExprFacF[B] =
        ea match
          case Left(xa) => Left(kittensExprFunctor.map(xa)(f))
          case Right(fa) => Right(kittensFacFunctor.map(fa)(f))

  def inL[R](xa: ExprF[R]) = Left(xa)
  def inR[R](fa: FacF[R, Long]) = Right(fa)
```

We have defined the two convenience methods `in`ject left (`inL`) and right (`inR`); the `factorial` corecursive algorithm is:

```Scala
import ExprFacF._

def factorial(n: Long): ExprFacF[Long] =
  if n <= 0
  then
    inL(OneF)
  else
    inR(FacF(n-1, n))
```

We can now execute `factorial` with the recursion schemes `ana` and `cata`:

```Scala
(ana(factorial) andThen cata(eval :+: evalʹ)).apply(5)
```

Of course, the `fibonacci` corecursive algorithm does not change its signature - the advantage of having coproducts:

```Scala
def fibonacci(n: Long): ExprF[Long] =
  if n <= 1
  then
    ValF(1L min (0L max n))
  else
    AddF(n-1, n-2)
```

[First](https://github.com/sjbiaga/kittens/blob/main/recursion-1-lambda-calculus/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/recursion-1-lambda-calculus/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/recursion-3-Cofree/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/recursion-4-Defer/README.md)
