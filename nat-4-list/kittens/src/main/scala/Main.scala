import cats.{ Eval, Monad, StackSafeMonad, ~> }
import cats.syntax.flatMap.*

implicit val kittensʹListMonad: Monad[ʹ.List] =
  import ʹ.List
  import List.*
  new StackSafeMonad[List]:
    override def pure[A](x: A): List[A] = x :: Nil
    override def map[A, B](fa: List[A])(f: A => B): List[B] = fa.map(f)
    override def flatMap[A, B](fa: List[A])(f: A => List[B]): List[B] = fa.flatMap(f)
    override def flatten[A](ffa: List[List[A]]): List[A] = ffa.flatten
    // override def tailRecM[A, B](a: A)(f: A => List[Either[A, B]]): List[B] = // NOT stack safe!
    //   f(a).flatMap(_.fold(tailRecM(_)(f), _ :: Nil))
    // override def tailRecM[A, B](a: A)(f: A => List[Either[A, B]]): List[B] = // still NOT stack safe!
    //   f(a).foldRight(Nil: List[B]) {
    //     case (Left(a), bs) => tailRecM(a)(f) ::: bs
    //     case (Right(b), bs) => b :: bs
    //   }
    override def tailRecM[A, B](a: A)(f: A => List[Either[A, B]]): List[B] = // stack safe!
      def tailRecMʹ(a: A): Eval[List[B]] =
        def loop(ls: List[Either[A, B]], bs: List[B]): Eval[List[B]] =
          ls match
            case Nil =>
              Eval.now(bs)
            case Left(a) :: tl =>
              for
                _   <- Eval.Unit
                bsʹ <- tailRecMʹ(a)
                bs  <- loop(tl, bs ::: bsʹ)
              yield
                bs
            case Right(b) :: tl =>
              for
                _  <- Eval.Unit
                bs <- loop(tl, bs :+ b)
              yield
                bs
        loop(f(a), Nil)
      tailRecMʹ(a).value

def list: ʹ.List ~> List =
  new (ʹ.List ~> List):
    def apply[T](ls: ʹ.List[T]): List[T] =
      ls.toList

def listʹ: List ~> ʹ.List =
  new (List ~> ʹ.List):
    def apply[T](ls: List[T]): ʹ.List[T] =
      import ʹ.List.*
      ls.foldRight(Nil: ʹ.List[T])(_ :: _)

object Main:

  def main(args: Array[String]): Unit =
    println(listʹ(2 :: 4 :: 6 :: Nil))
    println(listʹ(List((1 to 10000)*)).size)
    try
      import ʹ.List
      import List.*
      println(List(1, 2, 3))
      ((1 :: 2 :: Nil) ::: (3 :: Nil)).foreach(println)
      println((1 :: 2 :: 3 :: Nil).map { it => List(it + it, it * it) }.flatten)
      println {
        for
          i <- (0 :: 1 :: 2 :: 3 :: Nil).tail
          j <- (2 :: 9 :: 16 :: 0 :: Nil).init
        yield
          i * j
      }
      println(list(List((1 to 10000)*)).size)
      kittensʹListMonad.tailRecM(())(Function.const(Left(()) :: Nil))
    catch
      case _: StackOverflowError =>
        ???
