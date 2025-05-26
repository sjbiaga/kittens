  import alleycats.{ Zero => `0`, One => `1` }

import cats.data.Reader

import Expr._

object Main:

  type Exprʹ[T] = Reader[String, Expr[T]]

  final case class Builder[T](lhs: Exprʹ[T], private var save: List[Exprʹ[T]]):
    def build(x: String): Expr[T] = lhs.run(x)
    def fill(n: Int) = List.fill(0 max n)(())
    def add(rhs: Expr[T], n: Int = 1) =
      Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Add(_, rhs)) }, save)
    def add(x: String)(using rhs: Exprʹ[T]) =
      Builder(rhs.map(Add(build(x), _)), save)
    def subtract(rhs: Expr[T], n: Int = 1) =
      Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Sub(_, rhs)) }, save)
    def subtract(x: String)(using rhs: Exprʹ[T]) =
      Builder(rhs.map(Sub(build(x), _)), save)
    def multiply(rhs: Expr[T], n: Int = 1) =
      Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Mul(_, rhs)) }, save)
    def multiply(x: String)(using rhs: Exprʹ[T]) =
      Builder(rhs.map(Mul(build(x), _)), save)
    def divide(rhs: Expr[T], n: Int = 1) =
      Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Div(_, rhs)) }, save)
    def divide(x: String)(using rhs: Exprʹ[T]) =
      Builder(rhs.map(Div(build(x), _)), save)
    def invert(n: Int = 1): Builder[T] =
      Builder(fill(n).foldLeft(lhs) { (lhs, _) => lhs.map(Inv(_)) }, save)
    def inject(x: String)(f: (Builder[T], String) => Exprʹ[T] ?=> Builder[T])(using Exprʹ[T]) =
      f(this, x)
    def open(using lhs: Exprʹ[T]) = Builder(lhs, this.lhs :: save)
    def close(x: String)(f: (Builder[T], Expr[T]) => Builder[T], invert: Int = 0) =
      require(save.nonEmpty)
      val self = Builder(save.head, save.tail)
      f(self, build(x)).invert(invert)
  object Builder:
    def start[T](using lhs: Exprʹ[T]) = Builder(lhs, Nil)

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
      import Exprʹ._

      val start = System.currentTimeMillis

      given Exprʹ[Double] = Reader(parseAll(expr, _).get)

      val x = Builder.start
        .add(One)
        .inject("2 - 2")(_.subtract(_))
        .multiply(Val(5d), 4)
          .open
          .add(One, 2)
          .close("7 / 5")(_.add(_))
        .build("(1 - 0) * (1 + 0)")

      val end = System.currentTimeMillis

      println(s"${elapsed(start, end)} $x ${eval(x)}")
    }

    {
      import Exprʹʹ._

      val start = System.currentTimeMillis

      given Exprʹ[Double] = Reader(parserExpr.parseAll(_).right.get)

      val x = Builder.start
        .add(One)
        .inject("2 - 2")(_.subtract(_))
        .multiply(Val(5d), 4)
          .open
          .add(One, 2)
          .close("7 / 5")(_.add(_))
        .build("(1 - 0) * (1 + 0)")

      val end = System.currentTimeMillis

      println(s"${elapsed(start, end)} $x ${eval(x)}")
    }

    {
      val start = System.currentTimeMillis

      val r =
        for
          lhs <- {
            import Exprʹ._

            given Exprʹ[Double] = Reader(parseAll(expr, _).get)

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

            given Exprʹ[Double] = Reader(parserExpr.parseAll(_).right.get)

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

      val x = r("(1 - 0) * (1 + 0)")

      val end = System.currentTimeMillis

      println(s"${elapsed(start, end)} $x ${eval(x)}")
    }
