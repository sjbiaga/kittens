import alleycats.{ Zero => `0`, One => `1` }

import cats.Eval
import cats.data.IndexedState

import Expr.*
import Tree.*

object Mainʹ:

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

    var expr = IndexedState.apply { (xa: Expr[Double]) => treeify.apply(xa) -> eval(xa) }
    var tree = IndexedState { (ta: Tree[Double]) => expressify.apply(ta) -> ta.result }

    println {
      ( for
          _ <- expr
          _ <- tree
          x <- expr
        yield
          x.toInt
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

    expr.flatMap[Int, Tree[Double]] { _ =>    // x0
      tree.flatMap[Int, Tree[Double]] { _ =>  // t1
        expr.map[Int] { x =>                  // x2
          x.toInt
        }
      }
    }

    val x2: IndexedState[Expr[Double], Tree[Double], Int] = (expr: IndexedState[Expr[Double], Tree[Double], Double]).map[Int] { x =>
      x.toInt
    }

    val t1: IndexedState[Tree[Double], Tree[Double], Int] = (tree: IndexedState[Tree[Double], Expr[Double], Double]).flatMap[Int, Tree[Double]] { _ =>
      x2: IndexedState[Expr[Double], Tree[Double], Int]
    //                 1st1st1st1st                                                           2nd2nd2nd2nd
    }

    val x0: IndexedState[Expr[Double], Tree[Double], Int] = (expr: IndexedState[Expr[Double], Tree[Double], Double]).flatMap[Int, Tree[Double]] { _ =>
      t1: IndexedState[Tree[Double], Tree[Double], Int]
    //                 1st1st1st1st                                                           2nd2nd2nd2nd
    }

    lazy val list: LazyList[Unit] = () #:: list

    println {
      list.take(3).foldLeft(Left(x): Expr[Double] Either Tree[Double]) {
        case (Left(xa), _)  => Right(expr.run(xa).value._1)
        case (Right(ta), _) => Left(tree.run(ta).value._1)
      }.right.get
    }
