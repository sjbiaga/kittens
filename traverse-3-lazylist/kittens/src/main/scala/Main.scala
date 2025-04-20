package Exercise_07_2

import cats.{ Applicative, Eval, Traverse }
import cats.instances.option._
import cats.syntax.traverse._

implicit val kittensLazyListTraverse: Traverse[LazyList] =
  new Traverse[LazyList]:
    def traverse[G[_], A, B](fa: LazyList[A])(f: A => G[B])(implicit G: Applicative[G]): G[LazyList[B]] =
      Eval.now(fa).flatMap { s =>
        foldRight(s, Eval.always(G.pure(LazyList.empty[B]))) { (a, lgsb) =>
          G.map2Eval(f(a), lgsb) {
            (it, ls) =>
              it #:: ls
          }
        }
      }.value
    def foldRight[A, B](fa: LazyList[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
      if fa.isEmpty
      then
        lb
      else
        val rhs = Eval
          .defer {
            Eval
              .now(fa.tail)
              .flatMap {
                foldRight(_, lb)(f)
              }
          }
        f(fa.head, rhs)
    override def foldLeft[A, B](fa: LazyList[A], b: B)(f: (B, A) => B): B = ???

object Main:
  def main(args: Array[String]): Unit =
    try

      def fibonacci(a: Long, b: Long): LazyList[Long] =
        a #:: fibonacci(b, a + b)

      println {
        fibonacci(0, 1).take(4).traverse[cats.Id, Long](identity).toList
      }

    catch
      case _: StackOverflowError =>
        ???
