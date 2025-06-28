import cats.data.Validated

import Expr.*
import cats.data.Validated.{ Valid, Invalid }

object Main:

  def main(args: Array[String]): Unit =
    given unit = One

    val x = x"-(1.5+4-2)*3"
    val x0 = x"-(1.5/0+4/0-2/0)*3 / 0"

    {
      try
        val Valid(expr, log) = x.listen.value
        println(s"interpolated: ${expr} log:\n${log}")
      catch _ =>
        val Invalid(err) = x.listen.value
        println(s"interpolated: null log:${err.mkString("\n", "\n", "\n")}")
    }

    {
      val Valid(d, _) = x.listen.value
      val xʹ =
        Builder.start[Double](d)
        .add(One)
        .multiply(Val(5d), 4)
          .open(One)
          .add(One, 4)
            .open(One)
            .add(One, 5)
              .open(One)
              .add(One, 6)
              .invert(2)
              .close(_.add(_), 4)
            .close(_.add(_), 3)
          .close(_.add(_), 2)
        .swapping
        .lhs

      try
        val Valid(expr, log) = xʹ.listen.value
        println(s"built: ${expr} log:\n${log}")
      catch _ =>
        val Invalid(err) = xʹ.listen.value
        println(s"built: null log:${err.mkString("\n", "\n", "\n")}")
    }

    {
      val Valid(d, _) = x.listen.value
      val xʹ =
        Builder.start[Double](d)
        .add(One)
        .multiply(Val(5d), 4)
          .openʹ(One)
          .add(One, 4)
            .openʹ(One)
            .add(One, 5)
              .openʹ(One)
              .divide(Zero, 6)
              .invert(2)
              .closeʹ(_.addʹ(_), 4)
            .closeʹ(_.addʹ(_), 3)
          .closeʹ(_.addʹ(_), 2)
        .swapping
        .lhs

      try
        val Valid(expr, log) = xʹ.listen.value
        println(s"built: ${expr} log:\n${log}")
      catch _ =>
        val Invalid(err) = xʹ.listen.value
        println(s"builtʹ: null log:${err.mkString("\n", "\n", "\n")}")
    }

    {
      val Valid(d, _) = x.listen.value
      val xʹ =
        Builder.start[Double](d)
        .add(One)
        .divide(Zero, 4)
          .openʹ(One)
          .addʹ(x0, 2)
          .closeʹ(_.addʹ(_))
        .swapping
        .lhs

      try
        val Valid(expr, log) = xʹ.listen.value
        println(s"built: ${expr} log:\n${log}")
      catch _ =>
        val Invalid(err) = xʹ.listen.value
        println(s"builtʹ: null log:${err.mkString("\n", "\n", "\n")}")
    }
