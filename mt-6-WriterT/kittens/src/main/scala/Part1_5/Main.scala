package Exercise_08_1
package Part1_5

import cats.{ ~>, Eval, Monad, Show }

import cats.data.NonEmptyList

import cats.instances.option._
import cats.syntax.coflatMap._
import cats.syntax.flatMap._
import cats.syntax.partialOrder._

import Expr._

object Main:

  def main(args: Array[String]): Unit =
    given unit = Zero

    val x = x"(1.5+4-2)*3"

    {
      val (expr, log) = x.listen.value
      println(s"interpolated: ${expr} log:\n${log}")
    }

    {
      val xʹ =
        Builder.start(x)
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

      val (expr, log) = xʹ.listen.value
      println(s"built: ${expr} log:\n${log}")
    }

    {
      val xʹ =
        Builder.start(x)
        .add(One)
        .multiply(Val(5d), 4)
          .openʹ(One)
          .add(One, 4)
            .openʹ(One)
            .add(One, 5)
              .openʹ(One)
              .add(One, 6)
              .invert(2)
              .closeʹ(_.addʹ(_), 4)
            .closeʹ(_.addʹ(_), 3)
          .closeʹ(_.addʹ(_), 2)
        .swapping
        .lhs

      val (expr, log) = xʹ.listen.value
      println(s"builtʹ: ${expr} log:\n${log}")
    }

    {
      val xʹ =
        Builder.start(x)
        .add(One)
        .multiply(Val(5d), 4)
          .openʹ(One)
          .addʹ(x, 2)
          .add(One, 2)
            .openʹ(One)
            .addʹ(x, 2)
            .closeʹ(_.addʹ(_, 2))
          .closeʹ(_.addʹ(_))
        .swapping
        .lhs

      val (expr, log) = xʹ.listen.value
      println(s"builtʹ: ${expr} log:\n${log}")
    }

    {
      val (expr, log) = eval(x.value.asInstanceOf[Expr[Double]]).listen.value
      println(s"evaluated: ${expr} log:\n${log}")
    }

    {
      val (_, log) = x.listen.value
      val (_, logʹ) = eval(x.value.asInstanceOf[Expr[Double]]).listen.value
      var ls = log.split("\n")
      val lsʹ = logʹ.split("\n")
      ls = ls.filterNot(_ == "parentheses")
      println(s"""zipped:\n${(ls zip lsʹ).mkString("\n")}""")
    }
