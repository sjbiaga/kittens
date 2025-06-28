import alleycats.{ Zero => `0`, One => `1` }

import cats.{ Applicative, Eval, Monad, Traverse }
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
  import scala.util.control.TailCalls.*
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
            case Val(it)   => done(Val(f(it)))
            case Add(m, n) =>
              for
                mʹ <- tailcall { mapʹ(m) }
                nʹ <- tailcall { mapʹ(n) }
              yield
                Add(mʹ, nʹ)
            case Sub(m, n) =>
              for
                mʹ <- tailcall { mapʹ(m) }
                nʹ <- tailcall { mapʹ(n) }
              yield
                Sub(mʹ, nʹ)
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
              case Val(Left(a))      =>
                for
                  _  <- Eval.Unit
                  xb <- tailRecMʹ(a)
                yield
                  xb
              case Val(Right(b))     =>
                Eval.now(Val(b))
              case Inv(xn)           =>
                for
                  _ <- Eval.Unit
                  n <- loop(xn)
                yield
                  Inv(n)
              case Add(xm, xn)       =>
                for
                  _ <- Eval.Unit
                  m <- loop(xm)
                  n <- loop(xn)
                yield
                  Add(m, n)
              case Sub(xm, xn)       =>
                for
                  _ <- Eval.Unit
                  m <- loop(xm)
                  n <- loop(xn)
                yield
                  Sub(m, n)
              case Mul(xm, xn)       =>
                for
                  _ <- Eval.Unit
                  m <- loop(xm)
                  n <- loop(xn)
                yield
                  Mul(m, n)
              case Div(xm, xn)       =>
                for
                  _ <- Eval.Unit
                  m <- loop(xm)
                  n <- loop(xn)
                yield
                  Div(m, n)
          loop(f(a))
        tailRecMʹ(a).value

  implicit def kittensExprTraverse(implicit `0`: `0`[?], `1`: `1`[?]): Traverse[Expr] =
    new Traverse[Expr]:
      override def foldLeft[A, B](fa: Expr[A], b: B)(f: (B, A) => B): B =
        implicit val `0ʹ`: `0`[A] = `0`.asInstanceOf[`0`[A]]
        implicit val `1ʹ`: `1`[A] = `1`.asInstanceOf[`1`[A]]
        def foldLeftʹ(xa: Expr[A], b: B): TailRec[B] =
          xa match
            case Val(a)    => done(f(b, a))
            case Add(m, n) =>
              for
                b <- tailcall { foldLeftʹ(m, b) }
                b <- tailcall { foldLeftʹ(n, b) }
              yield
                b
            case Sub(m, n) =>
              for
                b <- tailcall { foldLeftʹ(m, b) }
                b <- tailcall { foldLeftʹ(n, b) }
              yield
                b
            case Mul(m, n) =>
              for
                b <- tailcall { foldLeftʹ(m, b) }
                b <- tailcall { foldLeftʹ(n, b) }
              yield
                b
            case Div(m, n) =>
              for
                b <- tailcall { foldLeftʹ(m, b) }
                b <- tailcall { foldLeftʹ(n, b) }
              yield
                b
            case Inv(n)    =>
              for
                b <- tailcall { foldLeftʹ(n, b) }
              yield
                b
            case Zero      => done(f(b, `0ʹ`.zero))
            case One       => done(f(b, `1ʹ`.one))
        foldLeftʹ(fa, b).result
      override def foldRight[A, B](fa: Expr[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
        implicit val `0ʹ`: `0`[A] = `0`.asInstanceOf[`0`[A]]
        implicit val `1ʹ`: `1`[A] = `1`.asInstanceOf[`1`[A]]
        def foldRightʹ(xa: Expr[A], lb: Eval[B]): Eval[B] =
          xa match
            case Val(a)    => f(a, lb)
            case Add(m, n) =>
              Eval.defer { foldRightʹ(m, Eval.defer { foldRightʹ(n, lb) }) }
            case Sub(m, n) =>
              Eval.defer { foldRightʹ(m, Eval.defer { foldRightʹ(n, lb) }) }
            case Mul(m, n) =>
              Eval.defer { foldRightʹ(m, Eval.defer { foldRightʹ(n, lb) }) }
            case Div(m, n) =>
              Eval.defer { foldRightʹ(m, Eval.defer { foldRightʹ(n, lb) }) }
            case Inv(n)    =>
              Eval.defer { foldRightʹ(n, lb) }
            case Zero      => f(`0ʹ`.zero, lb)
            case One       => f(`1ʹ`.one, lb)
        foldRightʹ(fa, lb)
      override def traverse[G[_]: Applicative, A, B](fa: Expr[A])(f: A => G[B]): G[Expr[B]] =
        val G = Applicative[G]
        def traverseʹ(xa: Expr[A]): TailRec[G[Expr[B]]] =
          xa match
            case Val(it)   => done(G.map(f(it))(Val(_)))
            case Add(m, n) =>
              for
                mʹ <- tailcall { traverseʹ(m) }
                nʹ <- tailcall { traverseʹ(n) }
              yield
                G.map2(mʹ, nʹ)(Add(_, _))
            case Sub(m, n) =>
              for
                mʹ <- tailcall { traverseʹ(m) }
                nʹ <- tailcall { traverseʹ(n) }
              yield
                G.map2(mʹ, nʹ)(Sub(_, _))
            case Mul(m, n) =>
              for
                mʹ <- tailcall { traverseʹ(m) }
                nʹ <- tailcall { traverseʹ(n) }
              yield
                G.map2(mʹ, nʹ)(Mul(_, _))
            case Div(m, n) =>
              for
                mʹ <- tailcall { traverseʹ(m) }
                nʹ <- tailcall { traverseʹ(n) }
              yield
                G.map2(mʹ, nʹ)(Div(_, _))
            case Inv(n)    =>
              for
                nʹ <- tailcall { traverseʹ(n) }
              yield
                G.map(nʹ)(Inv(_))
            case it @ (Zero | One) => done(G.pure(it))
        traverseʹ(fa).result

  def show[A](xs: Expr[Set[A]])(implicit depth: Int = 0, `0`: `0`[Set[A]], `1`: `1`[Set[A]], uni: Set[A]): String =
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
        case Zero          => if `0`.zero.isEmpty then "∅" else `0`.zero.toString
        case One           => `1`.one.mkString("{ ", ", ", " }")
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

  implicit def eval[A](xs: Expr[Set[A]])(implicit `0`: `0`[Set[A]], `1`: `1`[Set[A]], uni: Set[A]): Set[A] =
    xs match
      case Zero          => `0`.zero
      case One           => `1`.one
      case Val(set)      => set
      case Inv(rhs)      => uni &~ rhs
      case Add(lhs, rhs) => lhs ++ rhs
      case Sub(lhs, rhs) => lhs &~ rhs
      case Mul(lhs, rhs) => lhs & rhs
      case Div(lhs, rhs) => (lhs &~ rhs) ++ (rhs &~ lhs)
