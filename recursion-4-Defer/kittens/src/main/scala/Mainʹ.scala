import Expr.*

import alleycats.{ Zero => `0`, One => `1` }

import cats.Eval, cats.data.Cont

object Mainʹ:

  def factorial(n: Long): Long =
    def factorialʹ(n: Long, f: Long): Cont[Long, Long] =
      for
        b <- Cont.defer(n == 0)
        r <- ( if b
               then
                 Cont.pure(f)
               else
                 for
                   m <- Cont.defer(n - 1)
                   p <- Cont.defer(n * f)
                   r <- factorialʹ(m, p)
                 yield
                   r
             )
      yield
        r
    factorialʹ(n, 1).eval.value

  def main(args: Array[String]): Unit =
    println(factorial(5))

    given unit = Zero // One

    given `0`[Double] = `0`(0d)
    given `1`[Double] = `1`(1d)

    val builderCont: Expr[Double] => Cont[Expr[Double], Expr[Double]] =
      xa => Cont.defer {
        Builder.start(xa)
        .add(One)
        .multiply(Val(5d), 4)
          .open(One)
          .add(One, 2)
          .close(_.add(_))
        .swapping
        .lhs
      }

    val builderContʹ: Expr[Double] => Cont[Expr[Double], Expr[Double]] =
      xa => Cont.defer {
        Builder.start(xa)
        .add(One)
        .multiply(Val(5d), 4)
          .open(One)
          .add(One, 4)
            .open(One)
            .add(One, 5)
              .open(One)
              .add(One, 6)
              .invert(2)
              .close(_.add(_, 2), 4)
            .close(_.add(_), 3)
          .close(_.add(_), 2)
        .swapping
        .lhs
      }

    def simplifyCont[A]: Expr[A] => Cont[Expr[A], Expr[A]] =
      simplify[A] andThen Cont.pure

    val evalCont: Expr[Double] => Cont[Expr[Double], Double] =
      eval andThen Cont.pure

    val divByZeroCont: Double => Cont[Expr[Double], String] =
      d => Cont.defer {
        if d == Double.PositiveInfinity || d == Double.NegativeInfinity
        then
          "Division by zero"
        else
          "No errors"
      }

    val c: Cont[Expr[Double], Double] =
      for
        x <- Cont.defer(Inv(x"(1.0-0.0) * (1.0+0.0)"))
        xʹ = x.asInstanceOf[Expr[Double]]
        x <- builderCont(xʹ)
        x <- simplifyCont(x)
        x <- builderContʹ(x)
        x <- simplifyCont(x)
        d <- evalCont(x)
        s <- divByZeroCont(d)
        _ <- Cont.defer(println(s))
      yield
        d

    println {
      c.run(Val.apply[Double] andThen Eval.later).value
    }

    val divByZeroContʹ: Double => Cont[Expr[Double], Double] =
      d => Cont.defer {
        if d == Double.PositiveInfinity || d == Double.NegativeInfinity
        then
          println("Division by zero")
          d
        else
          d
      }

    println { // nesting
      Cont
        .defer(Inv(x"(1.0-0.0) * (1.0+0.0)"))
        .flatMap { x =>
          val xʹ = x.asInstanceOf[Expr[Double]]
          builderCont(xʹ).flatMap {
            simplifyCont(_).flatMap {
              builderContʹ(_).flatMap {
                simplifyCont(_).flatMap {
                  evalCont(_).flatMap {
                    divByZeroContʹ(_).map(identity)
                  }
                }
              }
            }
          }
        }.run(Val.apply[Double] andThen Eval.later).value
    }

    println { // chaining
      import cats.syntax.flatMap.*
      {
        Cont.defer(Inv(x"(1.0-0.0) * (1.0+0.0)").asInstanceOf[Expr[Double]])
        >>= builderCont
        >>= simplifyCont
        >>= builderContʹ
        >>= simplifyCont
        >>= evalCont
        >>= divByZeroContʹ
      }.run(Val.apply[Double] andThen Eval.later).value
    }
