import alleycats.{ Zero => `0`, One => `1` }

import cats.{ Id, FlatMap, Monad }
import cats.data.ReaderT
import cats.free.Coyoneda

import Expr._

object Mainʹʹ:

  type Readerʹʹ[A, B] = ReaderT[[α] =>> Coyoneda[Id, α], A, B]

  type Exprʹʹʹ[T] = Readerʹʹ[String, Expr[T]]

  final case class Builder[T](lhs: Exprʹʹʹ[T], private var save: List[Exprʹʹʹ[T]]):
    def build(x: String): Expr[T] = lhs.run(x).run
    def fill(n: Int) = List.fill(0 max n)(())
    def add(rhs: Expr[T], n: Int = 1) =
      Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Add(_, rhs)) }, save)
    def add(x: String)(using rhs: Exprʹʹʹ[T]) =
      Builder(rhs.map(Add(build(x), _)), save)
    def subtract(rhs: Expr[T], n: Int = 1) =
      Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Sub(_, rhs)) }, save)
    def subtract(x: String)(using rhs: Exprʹʹʹ[T]) =
      Builder(rhs.map(Sub(build(x), _)), save)
    def multiply(rhs: Expr[T], n: Int = 1) =
      Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Mul(_, rhs)) }, save)
    def multiply(x: String)(using rhs: Exprʹʹʹ[T]) =
      Builder(rhs.map(Mul(build(x), _)), save)
    def divide(rhs: Expr[T], n: Int = 1) =
      Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Div(_, rhs)) }, save)
    def divide(x: String)(using rhs: Exprʹʹʹ[T]) =
      Builder(rhs.map(Div(build(x), _)), save)
    def invert(n: Int = 1): Builder[T] =
      Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Inv(_)) }, save)
    def inject(x: String)(f: (Builder[T], String) => Exprʹʹʹ[T] ?=> Builder[T])(using Exprʹʹʹ[T]) =
      f(this, x)
    def open(using lhs: Exprʹʹʹ[T]) = Builder(lhs, this.lhs :: save)
    def close(x: String)(f: (Builder[T], Expr[T]) => Builder[T], invert: Int = 0) =
      require(save.nonEmpty)
      val self = Builder(save.head, save.tail)
      f(self, build(x)).invert(invert)
  object Builder:
    def start[T](using lhs: Exprʹʹʹ[T]) = Builder(lhs, Nil)

  implicit def kittensCoyonedaFlatMap[F[_]](implicit F: Monad[F]): FlatMap[[α] =>> Coyoneda[F, α]] =
    new FlatMap[[α] =>> Coyoneda[F, α]] {
      override def flatMap[A, B](fa: Coyoneda[F, A])(f: A => Coyoneda[F, B]): Coyoneda[F, B] =
        flatten(map(fa)(f))

      override def flatten[A](ffa: Coyoneda[F, Coyoneda[F, A]]): Coyoneda[F, A] =
        Coyoneda.lift(F.flatMap(ffa.run)(_.run))

      override def tailRecM[A, B](a: A)(f: A => Coyoneda[F, Either[A, B]]): Coyoneda[F, B] =
        def loop(a: A): F[B] =
          F.tailRecM(a) { a =>
            F.flatMap(f(a).run) {
              case Left(a)      => F.map(loop(a))(Right.apply)
              case r @ Right(_) => F.pure(r)
            }
          }
        Coyoneda.lift(loop(a))

      override def map[A, B](fa: Coyoneda[F, A])(f: A => B): Coyoneda[F, B] =
        fa.map(f)
    }

  def elapsedʹ(start: Long, end: Long): (Long, Long, Long, Long) =
    val ms = (end - start) % 1000.0
    val ss = (end - start) / 1000.0
    val mm = ss / 60
    val hh = mm / 60
    (hh.toInt, (mm % 60).toInt, (ss % 60).toInt, ms.toInt)

  def elapsed(start: Long, end: Long): String =
    val (hh, mm, ss, ms) = elapsedʹ(start, end)
    s"$hh:$mm:$ss.$ms"

  def main(args: Array[String]): Unit =
    given unit = Zero

    given `0`[Double] = `0`(0d)
    given `1`[Double] = `1`(1d)

    {
      val start = System.currentTimeMillis

      val r =
        for
          lhs <- {
            import Exprʹ._

            given Exprʹʹʹ[Double] = ReaderT { x => Coyoneda.lift(parseAll(expr, x).get) }

            Builder.start
              .add(One)
              .inject("2 - 2")(_.subtract(_))
              .multiply(Val(5d), 4)
                .open
                .add(One, 2)
                .close("7 / 5")(_.add(_))
              .lhs
          }
          rhs <- {
            import Exprʹʹ._

            given Exprʹʹʹ[Double] = ReaderT { x => Coyoneda.lift(parserExpr.parseAll(x).right.get) }

            Builder.start
              .add(One)
              .inject("2 - 2")(_.subtract(_))
              .multiply(Val(5d), 4)
                .open
                .add(One, 2)
                .close("7 / 5")(_.add(_))
              .lhs
          }
        yield
          Div(lhs, rhs)

      val x = r("(1 - 0) * (1 + 0)").run

      val end = System.currentTimeMillis

      println(s"${elapsed(start, end)} $x ${eval(x)}")
    }
