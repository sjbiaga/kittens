import scala.util.control.TailCalls._
import scala.util.parsing.combinator.JavaTokenParsers

import alleycats.{ Zero => `0`, One => `1` }

import cats.{ ~>, Applicative, CoflatMap, Eval, Monad, Traverse, PartialOrder, Eq }
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

object Expr extends JavaTokenParsers:
  implicit val kittensExprMonad: Monad[Expr] =
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

  implicit val kittensExprCoflatMap: CoflatMap[Expr] =
    new CoflatMap[Expr]:
      def map[A, B](xa: Expr[A])(f: A => B): Expr[B] = kittensExprMonad.map(xa)(f)
      override def coflatten[A](fa: Expr[A]): Expr[Expr[A]] =
        def coflattenʹ[A](xa: Expr[A]): TailRec[Expr[Expr[A]]] =
          xa match
            case it @ Val(_)       => done(Val(it))
            case Add(m, n)         =>
              for
                mʹ <- tailcall { coflattenʹ(m) }
                nʹ <- tailcall { coflattenʹ(n) }
              yield
                Add(mʹ, nʹ)
            case Sub(m, n)         =>
              for
                mʹ <- tailcall { coflattenʹ(m) }
                nʹ <- tailcall { coflattenʹ(n) }
              yield
                Sub(mʹ, nʹ)
            case Mul(m, n)         =>
              for
                mʹ <- tailcall { coflattenʹ(m) }
                nʹ <- tailcall { coflattenʹ(n) }
              yield
                Mul(mʹ, nʹ)
            case Div(m, n)         =>
              for
                mʹ <- tailcall { coflattenʹ(m) }
                nʹ <- tailcall { coflattenʹ(n) }
              yield
                Div(mʹ, nʹ)
            case Inv(n)            =>
              for
                nʹ <- tailcall { coflattenʹ(n) }
              yield
                Inv(nʹ)
            case it @ (Zero | One) => done(it)
        coflattenʹ(fa).result
      def coflatMap[A, B](xa: Expr[A])(f: Expr[A] => B): Expr[B] =
        map(coflatten(xa))(f)

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

  implicit def kittensExprPartialOrder[A: PartialOrder]: PartialOrder[Expr[A]] =
    new PartialOrder[Expr[A]]:
      override def partialCompare(xa: Expr[A], ya: Expr[A]): Double =
        val OA = PartialOrder[A]
        def partialCompareʹ(x: Expr[A], y: Expr[A]): TailRec[Double] =
          (x, y) match
            case (Zero, One) => done(-1)
            case (One, Zero) => done(+1)
            case (Zero, Zero) | (One, One) => done(0)
            case (Val(n), Val(nʹ)) => done(OA.partialCompare(n, nʹ))
            case (Add(m, n), Add(mʹ, nʹ)) =>
              for
                i <- tailcall { partialCompareʹ(m, mʹ) }
                j <- tailcall { partialCompareʹ(n, nʹ) }
              yield
                if i == 0 then j else i
            case (Sub(m, n), Sub(mʹ, nʹ)) =>
              for
                i <- tailcall { partialCompareʹ(m, mʹ) }
                j <- tailcall { partialCompareʹ(n, nʹ) }
              yield
                if i == 0 then j else i
            case (Mul(m, n), Mul(mʹ, nʹ)) =>
              for
                i <- tailcall { partialCompareʹ(m, mʹ) }
                j <- tailcall { partialCompareʹ(n, nʹ) }
              yield
                if i == 0 then j else i
            case (Div(m, n), Div(mʹ, nʹ)) =>
              for
                i <- tailcall { partialCompareʹ(m, mʹ) }
                j <- tailcall { partialCompareʹ(n, nʹ) }
              yield
                if i == 0 then j else i
            case (Inv(n), Inv(nʹ)) =>
              for
                i <- tailcall { partialCompareʹ(n, nʹ) }
              yield
                i
            case _ => done(Double.NaN)
        partialCompareʹ(xa, ya).result

  implicit def kittensExprEq[A: Eq]: Eq[Expr[A]] =
    new Eq[Expr[A]]:
      override def eqv(xa: Expr[A], ya: Expr[A]): Boolean =
        val EA = Eq[A]
        def eqvʹ(x: Expr[A], y: Expr[A]): TailRec[Boolean] =
          (x, y) match
            case (Zero, Zero) | (One, One) => done(true)
            case (Val(n), Val(nʹ)) => done(EA.eqv(n, nʹ))
            case (Add(m, n), Add(mʹ, nʹ)) =>
              for
                e <- eqvʹ(m, mʹ)
                f <- eqvʹ(n, nʹ)
              yield
                e && f
            case (Sub(m, n), Sub(mʹ, nʹ)) =>
              for
                e <- eqvʹ(m, mʹ)
                f <- eqvʹ(n, nʹ)
              yield
                e && f
            case (Mul(m, n), Mul(mʹ, nʹ)) =>
              for
                e <- eqvʹ(m, mʹ)
                f <- eqvʹ(n, nʹ)
              yield
                e && f
            case (Div(m, n), Div(mʹ, nʹ)) =>
              for
                e <- eqvʹ(m, mʹ)
                f <- eqvʹ(n, nʹ)
              yield
                e && f
            case (Inv(n), Inv(nʹ)) =>
              for
                e <- eqvʹ(n, nʹ)
              yield
                e
            case _ => done(false)
        eqvʹ(xa, ya).result

  type unit = Expr.Zero.type | Expr.One.type

  def expr(implicit unit: unit): Parser[Expr[Int | Double]] =
    term ~ rep(("+"|"-") ~ term) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "+" ~ rhs) => Add(lhs, rhs)
        case (lhs, "-" ~ rhs) => Sub(lhs, rhs)
      }
    }

  def term(implicit unit: unit): Parser[Expr[Int | Double]] =
    factor ~ rep(("*"|"/") ~ factor) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "*" ~ rhs) => Mul(lhs, rhs)
        case (lhs, "/" ~ rhs) => Div(lhs, rhs)
      }
    }

  def factor(implicit unit: unit): Parser[Expr[Int | Double]] =
    ("+"|"-") ~ literal ^^ {
      case "-" ~ rhs if unit eq Zero => Inv(rhs)
      case "+" ~ rhs => Add(Zero, rhs)
      case "-" ~ rhs => Sub(Zero, rhs)
    } |
    literal

  def literal(implicit unit: unit): Parser[Expr[Int | Double]] =
    floatingPointNumber ^^ {
      _.toDouble match
        case 0d => Zero
        case 1d => One
        case n => Val(n)
    } |
    decimalNumber ^^ {
      _.toInt match
        case 0 => Zero
        case 1 => One
        case n => Val(n)
    } |
    "("~> expr <~")"

  implicit class ExprInterpolator(private val sc: StringContext) extends AnyVal:
    def x(args: Any*)(implicit unit: unit): Expr[Int | Double] =
      val inp = (sc.parts zip (args :+ "")).foldLeft("") {
        case (r, (p, a)) => r + p + a
      }
      parseAll(expr, inp).get

  def eval(expr: Expr[Double])(implicit unit: unit, `0`: `0`[Double], `1`: `1`[Double]): Double =
    def evalʹ(xa: Expr[Double]): TailRec[Double] =
      xa match
        case Zero => done(`0`.zero)
        case One => done(`1`.one)
        case Val(n) => done(n)
        case Inv(xn) if Zero eq unit =>
          for
            n <- tailcall { evalʹ(xn) }
          yield
            `0`.zero - n
        case Inv(xn) if One eq unit =>
          for
            n <- tailcall { evalʹ(xn) }
          yield
            `1`.one / n
        case Add(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            m + n
        case Sub(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            m - n
        case Mul(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            m * n
        case Div(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            m / n
    evalʹ(expr).result

  val swap: unit ?=> Expr ~> Expr =
    new (Expr ~> Expr):
      def apply[T](expr: Expr[T]): Expr[T] =
        def applyʹ(xa: Expr[T]): TailRec[Expr[T]] =
          xa match
            case Zero        => done(One)
            case One         => done(Zero)
            case Add(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Mul(m, n)
            case Sub(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Div(m, n)
            case Mul(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Add(m, n)
            case Div(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Sub(m, n)
            case Inv(Zero)
              if summon[unit] eq One => applyʹ(Div(One, Zero))
            case Inv(xn)     =>
              for
                n <- tailcall { applyʹ(xn) }
              yield
                Inv(n)
            case it          => done(it)
        applyʹ(expr).result

  final case class Builder[T](lhs: Expr[T], private var save: List[Expr[T]]):
    def fill(n: Int)(rhs: Expr[T]) = List.fill(0 max n)(rhs)
    def swapping(implicit unit: unit) = Builder(swap(lhs), save)
    def add(rhs: Expr[T], n: Int = 1) = Builder(fill(n)(rhs).foldLeft(lhs)(Add(_, _)), save)
    def subtract(rhs: Expr[T], n: Int = 1) = Builder(fill(n)(rhs).foldLeft(lhs)(Sub(_, _)), save)
    def multiply(rhs: Expr[T], n: Int = 1) = Builder(fill(n)(rhs).foldLeft(lhs)(Mul(_, _)), save)
    def divide(rhs: Expr[T], n: Int = 1) = Builder(fill(n)(rhs).foldLeft(lhs)(Div(_, _)), save)
    def invert(n: Int = 1): Builder[T] = Builder(List.fill(0 max n)(()).foldLeft(lhs) { (lhs, _) => Inv(lhs) }, save)
    def open = Builder.From(lhs :: save)
    def close(f: (Builder[T], Expr[T]) => Builder[T], invert: Int = 0) =
      val self = Builder(save.head, save.tail)
      f(self, lhs).invert(invert)
  object Builder:
    def start[T] = From[T](Nil)
    final case class From[T](save: List[Expr[T]]):
      def apply(lhs: Expr[T]): Builder[T] = Builder(lhs, save)

  extension [F[_]: Applicative, T](self: Expr[F[Expr[T]]])
    def flattenF: F[Expr[T]] =
      val F = Applicative[F]
      def flattenʹ(xf: Expr[F[Expr[T]]]): TailRec[F[Expr[T]]] =
        xf match
          case it @ (Zero | One) =>
            done(F.pure(it))
          case Val(fx)           =>
            done(fx)
          case Add(xm, xn)       =>
            for
              m <- tailcall { flattenʹ(xm) }
              n <- tailcall { flattenʹ(xn) }
            yield
              F.map2(m, n)(Add(_, _))
          case Sub(xm, xn)       =>
            for
              m <- tailcall { flattenʹ(xm) }
              n <- tailcall { flattenʹ(xn) }
            yield
              F.map2(m, n)(Sub(_, _))
          case Mul(xm, xn)       =>
            for
              m <- tailcall { flattenʹ(xm) }
              n <- tailcall { flattenʹ(xn) }
            yield
              F.map2(m, n)(Mul(_, _))
          case Div(xm, xn)       =>
            for
              m <- tailcall { flattenʹ(xm) }
              n <- tailcall { flattenʹ(xn) }
            yield
              F.map2(m, n)(Div(_, _))
          case Inv(xn)           =>
            for
              n <- tailcall { flattenʹ(xn) }
            yield
              F.map(n)(Inv(_))
      flattenʹ(self).result

  extension [A](self: Expr[A])
    def map[B](f: A => B): Expr[B] =
      Monad[Expr].map(self)(f)
    def flatMap[B](f: A => Expr[B]): Expr[B] =
      Monad[Expr].flatMap(self)(f)
    def exists(f: A => Boolean)(implicit `0`: `0`[A], `1`: `1`[A]): Boolean =
      def existsʹ(xa: Expr[A]): TailRec[Boolean] =
        xa match
          case Val(n)      =>
            done(f(n))
          case Add(xm, xn) =>
            for
              m <- tailcall { existsʹ(xm) }
              n <- tailcall { existsʹ(xn) }
            yield
              m || n
          case Sub(xm, xn) =>
            for
              m <- tailcall { existsʹ(xm) }
              n <- tailcall { existsʹ(xn) }
            yield
              m || n
          case Mul(xm, xn) =>
            for
              m <- tailcall { existsʹ(xm) }
              n <- tailcall { existsʹ(xn) }
            yield
              m || n
          case Div(xm, xn) =>
            for
              m <- tailcall { existsʹ(xm) }
              n <- tailcall { existsʹ(xn) }
            yield
              m || n
          case Inv(xn)     =>
            for
              n <- tailcall { existsʹ(xn) }
            yield
              n
          case Zero        =>
            done(f(`0`.zero))
          case One         =>
            done(f(`1`.one))
      existsʹ(self).result
    def forall(f: A => Boolean)(implicit `0`: `0`[A], `1`: `1`[A]): Boolean =
      def forallʹ(xa: Expr[A]): TailRec[Boolean] =
        xa match
          case Val(n)      =>
            done(f(n))
          case Add(xm, xn) =>
            for
              m <- tailcall { forallʹ(xm) }
              n <- tailcall { forallʹ(xn) }
            yield
              m && n
          case Sub(xm, xn) =>
            for
              m <- tailcall { forallʹ(xm) }
              n <- tailcall { forallʹ(xn) }
            yield
              m && n
          case Mul(xm, xn) =>
            for
              m <- tailcall { forallʹ(xm) }
              n <- tailcall { forallʹ(xn) }
            yield
              m && n
          case Div(xm, xn) =>
            for
              m <- tailcall { forallʹ(xm) }
              n <- tailcall { forallʹ(xn) }
            yield
              m && n
          case Inv(xn)     =>
            for
              n <- tailcall { forallʹ(xn) }
            yield
              n
          case Zero        =>
            done(f(`0`.zero))
          case One         =>
            done(f(`1`.one))
      forallʹ(self).result
