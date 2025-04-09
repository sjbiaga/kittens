import cats._, cats.free._, Free._

case class Algorithms(n: Int, var counter: Int):
  private def fibonacci(k: Int): Trampoline[Int] =
    if k < 2
    then
      liftF { () => 1 min (0 max k) }
    else
      for
        m <- defer { fibonacci(k - 2) }
        n <- defer { fibonacci(k - 1) }
      yield
        n + m
  private def factorial(k: Int): Trampoline[Int] =
    if k < 1
    then
      liftF { () => 1 }
    else
      for
        n <- defer { factorial(k - 1) }
      yield
        k * n
  def fib: Trampoline[Int] = { counter = 0; fibonacci(n) }
  def fac: Trampoline[Int] = { counter = 0; factorial(n) }

class Function0ʹ[+R](f0: Function0[R]) extends Function0[R]:
  override def apply(): R =
    f0()

object Function0ʹ:
  implicit val kittensFunction0ʹBimonad: Bimonad[Function0ʹ] =
    new Bimonad[Function0ʹ]:
      def extract[A](fa: Function0ʹ[A]): A = fa()

      def coflatMap[A, B](fa: Function0ʹ[A])(f: Function0ʹ[A] => B): Function0ʹ[B] =
        Function0ʹ(() => f(fa))

      def pure[A](x: A): Function0ʹ[A] = Function0ʹ(() => x)

      override def map[A, B](fa: Function0ʹ[A])(fn: A => B): Function0ʹ[B] =
        Function0ʹ(() => fn(fa()))

      override def map2[A, B, C](fa: Function0ʹ[A], fb: Function0ʹ[B])(fn: (A, B) => C): Function0ʹ[C] =
        Function0ʹ(() => fn(fa(), fb()))

      override def product[A, B](fa: Function0ʹ[A], fb: Function0ʹ[B]): Function0ʹ[(A, B)] =
        Function0ʹ(() => (fa(), fb()))

      override def ap[A, B](f: Function0ʹ[A => B])(fa: Function0ʹ[A]): Function0ʹ[B] =
        Function0ʹ(() => f()(fa()))

      def flatMap[A, B](fa: Function0ʹ[A])(f: A => Function0ʹ[B]): Function0ʹ[B] =
        f(fa())

      def tailRecM[A, B](a: A)(fn: A => Function0ʹ[Either[A, B]]): Function0ʹ[B] =
        Function0ʹ(() => {
          @annotation.tailrec
          def loop(thisA: A): B =
            fn(thisA)() match {
              case Right(b)    => b
              case Left(nextA) => loop(nextA)
            }
          loop(a)
        })

  def counting(implicit as: Algorithms): Function0 ~> Function0ʹ =
    new (Function0 ~> Function0ʹ):
      def apply[T](f0: Function0[T]): Function0ʹ[T] =
        as.counter += 1
        new Function0ʹ(f0)

object Main:
  def main(args: Array[String]): Unit =
    implicit val as: Algorithms = Algorithms(20, 0)
    println(as.fib.mapK(Function0ʹ.counting).runTailRec()())
    println(as.counter)
