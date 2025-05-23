import Expr._

import alleycats.{ Zero => `0`, One => `1` }

import cats.Eval, cats.data.ContT

object Mainʹ:

  def factorial(n: Long): Long =
    def factorialʹ(n: Long, f: Long): ContT[Eval, Long, Long] =
      for
        b <- ContT.defer(n == 0)
        r <- ( if b
               then
                 ContT.pure(f)
               else
                 for
                   m <- ContT.defer(n - 1)
                   p <- ContT.defer(n * f)
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

    val builderContT: Expr[Double] => ContT[Eval, Expr[Double], Expr[Double]] =
      xa => ContT.defer {
        Builder.start(xa)
        .add(One)
        .multiply(Val(5d), 4)
          .open(One)
          .add(One, 2)
          .close(_.add(_))
        .swapping
        .lhs
      }

    val builderContTʹ: Expr[Double] => ContT[Eval, Expr[Double], Expr[Double]] =
      xa => ContT.defer {
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

    def simplifyContT[A]: Expr[A] => ContT[Eval, Expr[A], Expr[A]] =
      simplify[A] andThen ContT.pure

    val evalContT: Expr[Double] => ContT[Eval, Expr[Double], Double] =
      eval andThen ContT.pure

    val divByZeroContT: Double => ContT[Eval, Expr[Double], String] =
      d => ContT.defer {
        if d == Double.PositiveInfinity || d == Double.NegativeInfinity
        then
          "Division by zero"
        else
          "No errors"
      }

    val c: ContT[Eval, Expr[Double], Double] =
      for
        x <- ContT.defer(Inv(x"(1.0-0.0) * (1.0+0.0)"))
        xʹ = x.asInstanceOf[Expr[Double]]
        x <- builderContT(xʹ)
        x <- simplifyContT(x)
        x <- builderContTʹ(x)
        x <- simplifyContT(x)
        d <- evalContT(x)
        s <- divByZeroContT(d)
        _ <- ContT.defer(println(s))
      yield
        d

    println {
      c.run(Val.apply[Double] andThen Eval.later).value
    }

    val divByZeroContTʹ: Double => ContT[Eval, Expr[Double], Double] =
      d => ContT.defer {
        if d == Double.PositiveInfinity || d == Double.NegativeInfinity
        then
          println("Division by zero")
          d
        else
          d
      }

    println { // nesting
      ContT
        .defer(Inv(x"(1.0-0.0) * (1.0+0.0)"))
        .flatMap { x =>
          val xʹ = x.asInstanceOf[Expr[Double]]
          builderContT(xʹ).flatMap {
            simplifyContT(_).flatMap {
              builderContTʹ(_).flatMap {
                simplifyContT(_).flatMap {
                  evalContT(_).flatMap {
                    divByZeroContTʹ(_).map(identity)
                  }
                }
              }
            }
          }
        }.run(Val.apply[Double] andThen Eval.later).value
    }

    println { // chaining
      import cats.syntax.flatMap._
      {
        ContT.defer(Inv(x"(1.0-0.0) * (1.0+0.0)").asInstanceOf[Expr[Double]])
        >>= builderContT
        >>= simplifyContT
        >>= builderContTʹ
        >>= simplifyContT
        >>= evalContT
        >>= divByZeroContTʹ
      }.run(Val.apply[Double] andThen Eval.later).value
    }
