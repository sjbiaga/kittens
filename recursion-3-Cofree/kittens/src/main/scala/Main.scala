import alleycats.{ Zero => `0`, One => `1` }

import cats.free.Cofree, cats.Eval

import ExprF._

object Main:

  def factorial(n: Long): ExprF[Long] =
    if n <= 0
    then
      OneF
    else
      FacF(n-1, n)

  def fibonacci(n: Long): ExprF[Long] =
    if n == 0
    then
      ZeroF
    else if n == 1
    then
      OneF
    else
      AddF(n-1, n-2)

  def main(args: Array[String]): Unit =
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
