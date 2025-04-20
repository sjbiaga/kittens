package cats

import cats.data.Chain
import cats.syntax.traverse._

implicit val kittensʹListTraverse: Traverse[Exercise_07_5.ʹ.List] =
  import Exercise_07_5.ʹ.List
  import List._
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
          // }(f)) { chain => List(chain.toList*) }
    override def foldLeft[A, B](fa: List[A], b: B)(f: (B, A) => B): B =
      fa.foldLeft(b)(f)
    override def foldRight[A, B](fa: List[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
      fa.foldRightʹ(lb)(f)

object Mainʹ:
  def main(args: Array[String]): Unit =
    try
      import Exercise_07_5.ʹ.List
      import List._

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
