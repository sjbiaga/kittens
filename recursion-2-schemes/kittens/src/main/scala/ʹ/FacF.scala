package ʹ

import cats.Functor

case class FacF[+R, T](n: R, k: T)

object FacF:
  implicit def kittensFacFunctor[T]: Functor[[R] =>> FacF[R, T]] =
     new Functor[[R] =>> FacF[R, T]]:
       override def map[A, B](fa: FacF[A, T])(f: A => B): FacF[B, T] =
         fa match
           case FacF(n, k) => FacF(f(n), k)

  def evalʹ(fa: FacF[Long, Long]): Long =
    fa match
      case FacF(n, k) => n * k
