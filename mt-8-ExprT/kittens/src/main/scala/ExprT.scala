import alleycats.{ Zero => `0`, One => `1` }

import cats.{ ~>, Applicative, Bimonad, CoflatMap, Contravariant, Eval, Functor, FlatMap, Monad, Foldable, Traverse, PartialOrder, Eq }

import cats.data.Nested

import cats.syntax.coflatMap._
import cats.syntax.flatMap._
import cats.syntax.functor._

import Expr._

final case class ExprT[F[_], A](value: F[Expr[A]]):

  def map[B](f: A => B)(implicit F: Functor[F]): ExprT[F, B] =
    transform(_.map(f))

  def flatMap[B](f: A => ExprT[F, B])(implicit F: Monad[F]): ExprT[F, B] =
    flatMapF(f(_).value)

  def flatMapF[B](f: A => F[Expr[B]])(implicit F: Monad[F]): ExprT[F, B] =
    flatTransform(_.map(f).flattenF)

  def flatTransform[B](f: Expr[A] => F[Expr[B]])(implicit F: FlatMap[F]): ExprT[F, B] =
    ExprT(F.flatMap(value)(f))

  def transform[B](f: Expr[A] => Expr[B])(implicit F: Functor[F]): ExprT[F, B] =
    ExprT(F.map(value)(f))

  def subflatMap[B](f: A => Expr[B])(implicit F: Functor[F]): ExprT[F, B] =
    transform(_.flatMap(f))

  def cosubflatMap[B](f: Expr[A] => B)(implicit F: Bimonad[F]): ExprT[F, B] =
    transform(_.coflatMap(f))

  def mapK[G[_]](f: F ~> G): ExprT[G, A] = ExprT(f(value))

  def contramap[B](f: B => A)(implicit F: Contravariant[F]): ExprT[F, B] =
    ExprT(F.contramap(value)(_.map(f)))

  def swap(using unit: unit)(implicit F: Functor[F]): ExprT[F, A] =
    transform(Expr.swap(using unit).apply)

  def exists(f: A => Boolean)(implicit F: Functor[F], `0`: `0`[A], `1`: `1`[A]): F[Boolean] =
    F.map(value)(_.exists(f))

  def forall(f: A => Boolean)(implicit F: Functor[F], `0`: `0`[A], `1`: `1`[A]): F[Boolean] =
    F.map(value)(_.forall(f))

  def partialCompare(that: ExprT[F, A])(implicit po: PartialOrder[F[Expr[A]]]): Double =
    po.partialCompare(this.value, that.value)

  def ===(that: ExprT[F, A])(implicit eqf: Eq[F[Expr[A]]]): Boolean =
    Eq[ExprT[F, A]].eqv(this, that)

  def traverse[G[_]: Applicative, B](f: A => G[B])(implicit F: Traverse[F], `0`: `0`[A], `1`: `1`[A]): G[ExprT[F, B]] =
    Applicative[G].map(F.compose(using Traverse[Expr]).traverse(value)(f))(ExprT.apply)

  def foldLeft[B](b: B)(f: (B, A) => B)(implicit F: Traverse[F], `0`: `0`[A], `1`: `1`[A]): B =
    F.compose(using Foldable[Expr]).foldLeft(value, b)(f)

  def foldRight[B](lb: Eval[B])(f: (A, Eval[B]) => Eval[B])(implicit F: Traverse[F], `0`: `0`[A], `1`: `1`[A]): Eval[B] =
    F.compose(using Foldable[Expr]).foldRight(value, lb)(f)

  def toNested: Nested[F, Expr, A] = Nested(value)

  def flatten[B](implicit F: Monad[F], ev: A <:< ExprT[F, B]): ExprT[F, B] =
    flatMap(ev)

  def flattenF[B](implicit F: Monad[F], ev: A <:< F[Expr[B]]): ExprT[F, B] =
    flatMapF(ev)

  def coflatten(implicit F: Bimonad[F]): ExprT[F, ExprT[F, A]] =
    ExprT(F.map(value)(_.coflatten.map(F.pure).map(ExprT.apply)))

  def coflattenF(implicit F: CoflatMap[F]): ExprT[F, Expr[A]] =
    ExprT(F.map(value)(_.coflatten))

object ExprT:

  implicit def kittensExprTPartialOrder[F[_], A](implicit po: PartialOrder[F[Expr[A]]]): PartialOrder[ExprT[F, A]] =
    new PartialOrder[ExprT[F, A]]:
      override def partialCompare(x: ExprT[F, A], y: ExprT[F, A]): Double =
        x.partialCompare(y)

  implicit def kittensExprTEq[F[_], A](implicit eqf: Eq[F[Expr[A]]]): Eq[ExprT[F, A]] =
    new Eq[ExprT[F, A]]:
      override def eqv(x: ExprT[F, A], y: ExprT[F, A]): Boolean =
        eqf.eqv(x.value, y.value)
