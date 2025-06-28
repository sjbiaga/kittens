package cats

import cats.data.Chain
import cats.instances.list.catsStdInstancesForList
import cats.syntax.traverse.*

val kittensListTraverse: Traverse[List] =
  new Traverse[List]:
    override def traverse[G[_]: Applicative, A, B](fa: List[A])(f: A => G[B]): G[List[B]] =
      implicitly[Applicative[G]] match
        case G: StackSafeMonad[G] =>
          G.map(Traverse.traverseDirectly(fa)(f)(G)) { chain => List(chain.toList*) }
        case G: Applicative[G] =>
          // foldLeft(fa, G.pure(Nil: List[B])) { (acc, a) => G.map2(f(a), acc)(_ :: _) } // not short circuiting!
          foldRight(fa, Eval.always(G.pure(Nil: List[B]))) {
            (a, acc) =>
              G.map2Eval(f(a), acc)(_ :: _)
          }.value
          // G.map(Chain.traverseViaChain {
          //   val as = collection.mutable.ArrayBuffer[A]()
          //   as ++= fa.iterator
          //   kernel.instances.StaticMethods.wrapMutableIndexedSeq(as)
          // }(f))(_.toList)
    override def foldLeft[A, B](fa: List[A], b: B)(f: (B, A) => B): B =
      catsStdInstancesForList.foldLeft(fa, b)(f)
    def foldRight[A, B](fa: List[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
      catsStdInstancesForList.foldRight(fa, lb)(f)

object Main:

  def main(args: Array[String]): Unit =
    given Traverse[List] = kittensListTraverse
    try
      println {
        List((1 to 10)*)
          .traverse { n => if n % 3 == 0 then None else { println(n); Option(n * 2) } }
      }

      println {
        List((1 to 10000)*)
          .traverse { n => Option(n * 2) }
          .get
          .size
      }
    catch
      case it: StackOverflowError =>
        ???
