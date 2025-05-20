[First](https://github.com/sjbiaga/kittens/blob/main/recursion-1-lambda-calculus/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/recursion-2-schemes/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/recursion-4-Defer/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/recursion-4-Defer/README.md)

Lesson 09 - Recursion (cont'd)
==============================

Recursion Schemes in `Cats`
---------------------------

`Cats` has a `Cofree` `case class`, for which a typeclass instance of the `Comonad` typeclass is given:

```Scala
final case class Cofree[S[_], A](head: A, tail: Eval[S[Cofree[S, A]]]) {
  def map[B](f: A => B)(implicit S: Functor[S]): Cofree[S, B] =
    Cofree(f(head), tail.map(S.lift(_.map(f))))

  def coflatMap[B](f: Cofree[S, A] => B)(implicit S: Functor[S]): Cofree[S, B] =
    Cofree.anaEval(this)(_.tail, f)
}

object Cofree {
  implicit def catsFreeComonadForCofree[S[_]: Functor]: Comonad[Cofree[S, *]] =
    new Comonad[Cofree[S, *]] {
      final override def extract[A](p: Cofree[S, A]): A = p.head

      final override def coflatMap[A, B](a: Cofree[S, A])(f: Cofree[S, A] => B): Cofree[S, B] = a.coflatMap(f)

      final override def coflatten[A](a: Cofree[S, A]): Cofree[S, Cofree[S, A]] = coflatMap(identity)

      final override def map[A, B](a: Cofree[S, A])(f: A => B): Cofree[S, B] = a.map(f)
    }
}
```

Note that `Cofree` does _not_ have a typeclass instance of the `Monad` typeclass, because it lacks a `flatMap` method; we
could attempt a definition:

```Scala
def flatMap[B](f: A => Cofree[S, B])(implicit S: FlatMap[S]): Cofree[S, B] =
  Cofree(f(a).head, tail.map(S.lift(_.flatMap(f))))
//         ^  does not compile
```

but we would not have what to put in place of the argument `a` to `f`.

The recursion schemes `ana` and `cata` are defined in the `Cofree` companion object:

```Scala
object Cofree {
  def ana[F[_]: Functor, A, B](a: A)(coalg: A => F[A], f: A => B): Cofree[F, B] =
    anaEval(a)(coalg andThen Eval.later, f)
  def anaEval[F[_], A, B](a: A)(coalg: A => Eval[F[A]], f: A => B)(implicit F: Functor[F]): Cofree[F, B] =
    Cofree[F, B](f(a), mapSemilazy(coalg(a))(F.lift(anaEval(_)(coalg, f))))

  private def mapSemilazy[A, B](fa: Eval[A])(f: A => B): Eval[B] =
    fa match {
      case Now(a) => Now(f(a))
      case _      => fa.map(f)
    }

  def cata[F[_], A, B](cof: Cofree[F, A])(folder: (A, F[B]) => Eval[B])(implicit F: Traverse[F]): Eval[B] =
    F.traverse(cof.tailForced)((cata(_)(folder)) andThen Eval.defer).flatMap(folder(cof.head, _))
}
```

`ana` prompts for a typeclass instance `Functor[F]`, while `cata` asks for a typeclass instance `Traverse[F]` - where `F` in
our case will be `ExprF`: both are stack safe.

In order to use the above recursion schemes for the same corecursive algorithms - and coalgebras - `factorial` and `fibonacci`
already [given](https://github.com/sjbiaga/kittens/blob/main/recursion-2-schemes/README.md#recursion-schemes-in-scala), we
need to provide with typeclass instances `Functor[ExprF]` and `Traverse[ExprF]`:

```Scala
import cats.{ Applicative, Eval, Functor, Traverse }

import alleycats.{ Zero => `0`, One => `1` }

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
           case FacF(n, k)     => FacF(f(n), k)
           case it @ (ValF(_) | ZeroF | OneF) => it

  implicit def kittensExprFTraverse(implicit `0`: `0`[?], `1`: `1`[?]): Traverse[ExprF] =
    new Traverse[ExprF]:
      override def foldLeft[A, B](xa: ExprF[A], b: B)(f: (B, A) => B): B =
        implicit val `0ʹ`: `0`[A] = `0`.asInstanceOf[`0`[A]]
        implicit val `1ʹ`: `1`[A] = `1`.asInstanceOf[`1`[A]]
        xa match
          case ValF(n: A) => f(b, n)
          case AddF(m, n) => f(f(b, m), n)
          case SubF(m, n) => f(f(b, m), n)
          case MulF(m, n) => f(f(b, m), n)
          case DivF(m, n) => f(f(b, m), n)
          case InvF(n)    => f(b, n)
          case ZeroF      => f(b, `0ʹ`.zero)
          case OneF       => f(b, `1ʹ`.one)
          case FacF(n, _) => f(b, n)
      override def foldRight[A, B](xa: ExprF[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
        implicit val `0ʹ`: `0`[A] = `0`.asInstanceOf[`0`[A]]
        implicit val `1ʹ`: `1`[A] = `1`.asInstanceOf[`1`[A]]
        xa match
          case ValF(n: A) => f(n, lb)
          case AddF(m, n) => f(m, f(n, lb))
          case SubF(m, n) => f(m, f(n, lb))
          case MulF(m, n) => f(m, f(n, lb))
          case DivF(m, n) => f(m, f(n, lb))
          case InvF(n)    => f(n, lb)
          case ZeroF      => f(`0ʹ`.zero, lb)
          case OneF       => f(`1ʹ`.one, lb)
          case FacF(n, _) => f(n, lb)
      override def traverse[G[_]: Applicative, A, B](xa: ExprF[A])(f: A => G[B]): G[ExprF[B]] =
        val G = Applicative[G]
        xa match
          case ValF(n: A) => G.map(f(n))(ValF(_))
          case AddF(m, n) => G.map2(f(m), f(n))(AddF(_, _))
          case SubF(m, n) => G.map2(f(m), f(n))(SubF(_, _))
          case MulF(m, n) => G.map2(f(m), f(n))(MulF(_, _))
          case DivF(m, n) => G.map2(f(m), f(n))(DivF(_, _))
          case InvF(n)    => G.map(f(n))(InvF(_))
          case it @ (ZeroF | OneF) => G.pure(it)
          case FacF(n, k) => G.map(f(n))(FacF(_, k))

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

Now, we can perform the recursion for `factorial` and `fibonacci` using `Cofree`:

```Scala
import Cofree.{ ana, cata }

given `0`[Long] = `0`(0L)
given `1`[Long] = `1`(1L)

println {
  val fac: Cofree[ExprF, Long] = ana(5L)(factorial, identity)
  cata[ExprF, Long, Long](fac)((_, fb) => Eval.now(eval(fb))).value
}
println {
  val fib: Cofree[ExprF, Long] = ana(5L)(fibonacci, identity)
  cata[ExprF, Long, Long](fib)((_, fb) => Eval.now(eval(fb))).value
}
```

[First](https://github.com/sjbiaga/kittens/blob/main/recursion-1-lambda-calculus/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/recursion-2-schemes/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/recursion-4-Defer/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/recursion-4-Defer/README.md)
