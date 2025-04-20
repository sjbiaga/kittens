import alleycats.{ Zero, One }
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
