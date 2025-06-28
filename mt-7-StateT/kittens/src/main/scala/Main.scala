import alleycats.{ Zero => `0`, One => `1` }

import cats.data.State

import Expr.*

object Main:

  type Stateʹ = State[Expr[Double], Double]

  def main(args: Array[String]): Unit =
    given unit = Zero

    given `0`[Double] = `0`(0d)
    given `1`[Double] = `1`(1d)

    var x =
      Builder.start(x"0")
      .add(One)
      .multiply(Val(5d), 4)
        .open(One)
        .add(One, 2)
        .close(_.add(_))
      .lhs
      .asInstanceOf[Expr[Double]]

    val expr = State { (xa: Expr[Double]) => swap(xa) -> eval(xa) }

    println {
      ( for
          _ <- expr
          x <- expr
        yield
          x
      ).run(x).value
    }

    lazy val list: LazyList[Stateʹ] = expr #:: list

    println { list.take(3).foldRight(x)(_.run(_).value._1) }
