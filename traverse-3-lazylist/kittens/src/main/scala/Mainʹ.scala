package Exercise_07_3

import cats.{ Applicative, Eval, Traverse }
import cats.instances.option.catsStdInstancesForOption

import kittens.Trampoline, Trampoline.*

implicit val kittensOptionApplicative: Applicativeʹ[Option] =
  new Applicativeʹ[Option]:
    override def pure[A](x: A): Option[A] =
      catsStdInstancesForOption.pure(x)
    override def ap[A, B](ff: Option[A => B])(fa: Option[A]): Option[B] =
      catsStdInstancesForOption.ap(ff)(fa)

    override def map2Trampoline[A, B, Z](fa: Option[A], lb: Trampoline[Option[B]])(f: (A, B) => Z): Trampoline[Option[Z]] =
      fa match
        case None => Trampoline.pure(None)
        case Some(a) =>
          lb.map {
            case Some(b) =>
              Some(f(a, b))
            case None =>
              None
          }

trait Traverseʹ[F[_]] extends Traverse[F]:
  def traverseʹ[G[_]: Applicativeʹ, A, B](fa: F[A])(f: A => G[B]): G[F[B]]
  def foldRightʹ[A, B](fa: F[A], lb: Trampoline[B])(f: (A, Trampoline[B]) => Trampoline[B]): Trampoline[B]
  def foldRightʹʹ[A, B](fa: F[A], lb: Trampoline[B])(f: (A, Trampoline[B]) => Trampoline[B]): Trampoline[B]

implicit val kittensLazyListTraverseʹ: Traverseʹ[LazyList] =
  new Traverseʹ[LazyList]:
    override def traverse[G[_]: Applicative, A, B](fa: LazyList[A])(f: A => G[B]): G[LazyList[B]] = ???
    override def foldLeft[A, B](fa: LazyList[A], b: B)(f: (B, A) => B): B = ???
    override def foldRight[A, B](fa: LazyList[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] = ???
    def traverseʹ[G[_], A, B](fa: LazyList[A])(f: A => G[B])(implicit G: Applicativeʹ[G]): G[LazyList[B]] =
      foldRightʹ(fa, Trampoline.pure(G.pure(LazyList.empty[B]))) { (a, lgsb) =>
        G.map2Trampoline(f(a), lgsb)(_ #:: _)
      }()
    def foldRightʹ[A, B](fa: LazyList[A], lb: Trampoline[B])(f: (A, Trampoline[B]) => Trampoline[B]): Trampoline[B] =
      Trampoline.pure(fa).flatMap { s =>
        if s.isEmpty
        then
          lb
        else
          val rhs = Call(foldRightʹ(s.tail, lb)(f))
          f(s.head, rhs)
      }
    def foldRightʹʹ[A, B](fa: LazyList[A], lb: Trampoline[B])(f: (A, Trampoline[B]) => Trampoline[B]): Trampoline[B] =
      if fa.isEmpty
      then
        lb
      else
        val rhs = Call(foldRightʹʹ(fa.tail, lb)(f))
        f(fa.head, rhs)

object Mainʹ:

  def main(args: Array[String]): Unit =
    try

      def fibonacci(a: Long, b: Long): LazyList[Long] =
        a #:: fibonacci(b, a + b)

      println {
        val T = implicitly[Traverseʹ[LazyList]]
        T.traverseʹ[Option, Long, Long](fibonacci(0, 1).take(10))(Some(_)).get.toList
      }

      println {
        val T = implicitly[Traverseʹ[LazyList]]
        T.traverseʹ[Option, Long, Long](fibonacci(0, 1)) {
          it =>
            if it % 3 != 0
            then
              println(it)
              Some(it)
            else
              None
        }
      }

      println {
        val T = implicitly[Traverseʹ[LazyList]]
        T.traverseʹ[Option, Int, Int](LazyList((1 to 100000)*))(Option.apply)
          .get
          .size
      }

      println {
        try
          val T = implicitly[Traverseʹ[LazyList]]
          lazy val rec: (Long, Trampoline[Long]) => Trampoline[Long] =
            { (a, tb) => T.foldRightʹʹ(LazyList(a), tb)(rec) }
          T.foldRightʹʹ(LazyList(0L), Trampoline.Call(_ => ???))(rec)()
        catch
          case _: StackOverflowError =>
            "not stack safe!"
      }

    catch
      case _: StackOverflowError =>
        ???
