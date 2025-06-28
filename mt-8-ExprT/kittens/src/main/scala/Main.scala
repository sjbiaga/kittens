import alleycats.{ Zero => `0`, One => `1` }

import cats.{ ~>, Eval, Monad, Show }

import cats.data.NonEmptyList

import cats.instances.option.*
import cats.syntax.coflatMap.*
import cats.syntax.flatMap.*
import cats.syntax.partialOrder.*

import Expr.*
import ExprT.*

object Main:

  val opt2ls: Option ~> List =
    new (Option ~> List):
      override def apply[A](fa: Option[A]): List[A] =
        fa.map(_ :: Nil).getOrElse(Nil)

  case class Wrap[T](n: T)

  def main(args: Array[String]): Unit =
    given unit = Zero

    val x =
      Builder.start(x"0")
      .add(One)
      .multiply(Val(5d), 4)
        .open(One)
        .add(One, 2)
        .close(_.add(_))
      .swapping
      .lhs
      .asInstanceOf[Expr[Double]]

    given `0`[Double] = `0`(0d)
    given `1`[Double] = `1`(1d)

    val xoptT: ExprT[Option, Double] = ExprT(Option(x)).swap
    val xoptTʹ: ExprT[Option, Double] = xoptT.map(_ + 1)
    val xoptTʹʹ: ExprT[Option, Double] = xoptT.flatMap { n => xoptTʹ.map(_ / n) }
    val xoptTʹʹʹ: ExprT[Option, Double] = xoptT.subflatMap { n => x.map(_ * n) }
    val showIntExpr: Show[Expr[Int]] = xi => eval(xi.map(_ / 1000)).toInt.toString
    val xshowT = ExprT[Show, Int](showIntExpr)
    val xnelT: ExprT[NonEmptyList, Double] = ExprT(NonEmptyList(x, swap(x) :: Nil))
    val xnelTʹ: ExprT[NonEmptyList, Double] = xnelT.cosubflatMap(eval)

    println(eval(x)->x)
    println("\n")
    println(eval(xoptTʹ.value.get)->xoptTʹ.value)
    println("\n")
    println(eval(xoptTʹʹ.value.get)->xoptTʹʹ.value)
    println("\n")
    println(eval(xoptTʹʹʹ.value.get)->xoptTʹʹʹ.value)
    println("\n")
    println(eval(xoptT.value.get)->xoptT.mapK(opt2ls).value)
    println("\n")
    println(xshowT.contramap[Double](_.toInt).value.show(swap(x)))
    println("\n")
    println(xoptT.imap(Wrap.apply)(_.n))
    println("\n")
    println(xoptT.exists(_ == 5))
    println("\n")
    println(xoptT.forall(_ >= 0))
    println("\n")
    println(xoptT < xoptTʹ)
    println("\n")
    println(xoptT === xoptT)
    println("\n")
    println(xoptT.traverse(Option.apply))
    println("\n")
    println(xoptT.foldLeft(0d)(_ + _))
    println("\n")
    println(xoptT.foldRight(Eval.now(0d)) { (n, acc) => acc.map(n + _) }.value)
    println("\n")
    println(xoptT.toNested.mapK(opt2ls))
    println("\n")
    println(xnelT)
    println("\n")
    println(xnelT.coflatten)
    println("\n")
    println(xnelT.coflatten.flatten)
    println("\n")
    println(xnelTʹ)
    println("\n")
    println {
      for
        x <- xoptT
        y <- xoptTʹ
        z <- xoptTʹʹ
      yield
        x * y / z
    }
