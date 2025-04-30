import alleycats.{ Zero => `0`, One => `1` }

import cats.data.IndexedState

import Expr._
import Tree._

object Mainʹ:

  type Stateʹ[F[_], G[_]] = IndexedState[F[Double], G[Double], Double]

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

    val t = treeify.apply(x)

    var expr = IndexedState { (xa: Expr[Double]) => treeify.apply(xa) -> eval(xa) }
    var tree = IndexedState { (ta: Tree[Double]) => expressify.apply(ta) -> ta.result }

    println {
      ( for
          _ <- expr
          _ <- tree
          x <- expr
        yield
          x
      ).run(x).value
    }

    println {
      ( for
          _ <- tree
          _ <- expr
          t <- tree
        yield
          t
      ).run(t).value
    }

    lazy val list: LazyList[Stateʹ[Expr, Tree]] = expr #:: list
    lazy val listʹ: LazyList[Stateʹ[Tree, Expr]] = tree #:: listʹ

    println {
      (list zip listʹ).take(3).foldLeft(Left(x): Expr[Double] Either Tree[Double]) {
        case (Left(expr), (self, _))  => Right(self.run(expr).value._1)
        case (Right(tree), (_, self)) => Left(self.run(tree).value._1)
      }.right.get
    }
