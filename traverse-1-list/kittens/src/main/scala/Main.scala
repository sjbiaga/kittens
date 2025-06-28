import cats.{ Applicative, Eval, Id, Traverse }

import cats.syntax.traverse.*

implicit def kittensTuple5Traverse[W, X, Y, Z]: Traverse[[A] =>> Tuple5[W, X, Y, Z, A]] =
  new Traverse[[A] =>> Tuple5[W, X, Y, Z, A]]:
    def traverse[G[_], A, B](fwxyza: (W, X, Y, Z, A))(f: A => G[B])(implicit G: Applicative[G]): G[(W, X, Y, Z, B)] =
      val (w, x, y, z, a) = fwxyza
      G.map(f(a))((w, x, y, z, _))
    override def foldLeft[A, B](fwxyza: (W, X, Y, Z, A), b: B)(f: (B, A) => B): B =
      f(b, fwxyza._5)
    override def foldRight[A, B](fwxyza: (W, X, Y, Z, A), lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
      f(fwxyza._5, lb)

object Main:
  def main(args: Array[String]): Unit =
    println {
      (None, None, None, None, Some(5)).traverse[Option, Int](_.map(_ + 5))
    }
