package cats
package data

import cats.syntax.flatMap._
import cats.syntax.traverse._

def kittensʹtraverseViaChain[G[_], A, B](
  as: scala.collection.immutable.IndexedSeq[A]
)(f: A => G[B])(implicit G: Applicative[G]): G[Chain[B]] =
  if as.isEmpty then G.pure(Chain.nil)
  else
    val width = 8
    def loop(start: Int, end: Int): Eval[G[Chain[B]]] =
      if end - start <= width
      then
        var flist = Eval.later {
           G.map(f(as(end - 1))) {
            it =>
              it :: Nil
           }
        }
        var idx = end - 2
        while start <= idx
        do
          val a = as(idx)
          val rhs = flist
          flist = Eval.defer {
            G.map2Eval(f(a), rhs) {
              (it, ls) =>
                it :: ls
            }
          }
          idx = idx - 1
        flist.map { ls =>
          G.map(ls) { it =>
            Chain.fromSeq(it)
          }
        }
      else
        val step = (end - start) / width

        var fchain = Eval.defer {
          loop(start, start + step)
        }
        var start0 = start + step
        var end0 = start0 + step

        while start0 < end
        do
          val end1 = math.min(end, end0)
          val rhs = loop(start0, end1)
          fchain = fchain.flatMap { gchain =>
            G.map2Eval(gchain, rhs) {
              (lhs, rhs) =>
                lhs ++ rhs
            }
          }
          start0 = start0 + step
          end0 = end0 + step
        fchain

    { val half = as.size / 2
      if 0 < half && half < as.size
      then
        for
          fst <- Eval.defer { loop(0, half) }
          snd <- Eval.later { loop(half, as.size) }
          res <- G.map2Eval(fst, snd)(_ ++ _)
        yield
          res
      else
        loop(0, as.size)
    }.value

implicit val kittensʹListTraverse: Traverse[Exercise_07_6.ʹ.List] =
  import Exercise_07_6.ʹ.List
  import List._
  new Traverse[List]:
    override def traverse[G[_]: Applicative, A, B](fa: List[A])(f: A => G[B]): G[List[B]] =
      implicitly[Applicative[G]] match
        case G: StackSafeMonad[G] =>
          G.map(Traverse.traverseDirectly(fa)(f)(G)) { chain => List(chain.toList*) }
        case G: Applicative[G] =>
          G.map(kittensʹtraverseViaChain {
            val as = collection.mutable.ArrayBuffer[A]()
            as ++= fa.iterator
            kernel.instances.StaticMethods.wrapMutableIndexedSeq(as)
          }(f)) { chain => List(chain.toList*) }
    override def foldLeft[A, B](fa: List[A], b: B)(f: (B, A) => B): B =
      fa.foldLeft(b)(f)
    override def foldRight[A, B](fa: List[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
      fa.foldRightʹ(lb)(f)

object Main:
  def main(args: Array[String]): Unit =
    try
      import Exercise_07_6.ʹ.List
      import List._

      val G = implicitly[Applicative[Option]]

      val f: Int => Option[Int] = {
          it =>
            if it % 7 != 0
            then
              println(it)
              Some(it)
            else None
      }

      println {
        var flist = Eval.later {
          println(1)
          G.map(f(1000)) {
            it =>
              println(2)
              it :: Nil
          }
        }
        flist     = {
          val rhs1000 = flist
          Eval.defer {
            println(3)
            G.map2Eval(f(100), rhs1000) {
              (it, ls) =>
                println(4)
                it :: ls
            }
          }
        }
        flist     = {
          val rhs100 = flist
          Eval.defer {
            println(5)
            G.map2Eval(f(10), rhs100) {
              (it, ls) =>
                println(6)
                it :: ls
            }
          }
        }
        flist.map(identity).value
      }

      println {
        List((1 to 8)*).traverse {
          it =>
            if it % 7 != 0
            then
              println(it)
              Some(it)
            else None
          }
      }
    catch
      case _: StackOverflowError =>
        ???
