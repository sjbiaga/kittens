import algebra.ring.DivisionRing
import cats.{ Eval, Monad }

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
          case it @ (Zero | One) => it
      override def map[A, B](fa: Expr[A])(f: A => B): Expr[B] =
        fa match
          case Val(it)   => Val(f(it))
          case Add(n, m) => Add(map(n)(f), map(m)(f))
          case Sub(n, m) => Sub(map(n)(f), map(m)(f))
          case Mul(n, m) => Mul(map(n)(f), map(m)(f))
          case Div(n, m) => Div(map(n)(f), map(m)(f))
          case Inv(n)    => Inv(map(n)(f))
          case it @ (Zero | One) => it
      def flatMap[A, B](fa: Expr[A])(f: A => Expr[B]): Expr[B] =
        flatten(map(fa)(f))
      // def tailRecM[A, B](a: A)(f: A => Expr[Either[A, B]]): Expr[B] = // NOT stack safe!
      //   flatMap(f(a))(_.fold(tailRecM(_)(f), pure))
      def tailRecM[A, B](a: A)(f: A => Expr[Either[A, B]]): Expr[B] = // stack safe!
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
