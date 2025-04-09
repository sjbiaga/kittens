[Previous](https://github.com/sjbiaga/kittens/blob/main/expr-eert/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/eval-2-expr-tree/README.md)

Lesson 06: Natural Transformations (cont'd)
===========================================

Exercise 06.5
-------------

The `Trampoline` type is defined in `Cats` as:

```Scala
package cats

type Trampoline[A] = Free[Function0, A]
```

where `Function0[A]`, or `() => A`, is a function type without arguments; then it follows that the definition of `Suspend`:

```Scala
package cats
package free

object Free {
  final private[free] case class Suspend[S[_], A](a: S[A]) extends Free[S, A]
}
```

for `Function0[_]` is actually `Suspend[A](closure: () => A)`, which is very similar with `Call[A](closure: Unit => A)`, just
as we have seen at the beginning of [Lesson 06](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md), in
the implementation of our own `Trampoline`.

Check that there exists a `Cats` typeclass instance of the `Monad` typeclass for `Function0`; then, given the `Algorithms`
class with a `counter`:

```Scala
import cats._, cats.free._, cats.arrow._, Free._

case class Algorithms(n: Int, var counter: Int):
  private def fibonacci(k: Int): Trampoline[Int] =
    if k < 2
    then
      liftF { () => 1 min (0 max k) }
    else
      for
        m <- defer {  fibonacci(k - 2) }
        n <- defer {  fibonacci(k - 1) }
      yieldOB
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
```

define a `Function0ʹ[A]` class that wraps another function `() => A` - which it invokes on `apply` -, and uses it to implement
a natural transformation `counting` from `Function0` to `Function0ʹ`, that just counts in the above `counter` how many times
its `apply` method is invoked.

Solution
--------

To check for `Monad[Function0]`, simply wrap it in `implicitly`:

```scala
scala> implicitly[Monad[Function0]]
val res0: cats.Monad[[R] =>> () => R] = cats.instances.Function0Instances$$anon$4@11e36e5c
```

The `cats.instances.Function0Instances` is a trait containing the definition of:

```Scala
implicit val catsStdBimonadForFunction0: Bimonad[Function0] =
  new Bimonad[Function0] {
    ...
  }
```

We can replicate the same stack safe implementation of a typeclass instance of the `Bimonad` typeclass for `Function0ʹ`:

```Scala
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
```

Note that `flatMap` is the only method that does not wrap a function in `Function0ʹ`.

Now, the `counting` natural transformation creates a `Function0ʹ` from the argument to `apply`, incrementing `counter`:

```Scala
object Function0ʹ:
  def counting(implicit as: Algorithms): Function0 ~> Function0ʹ =
    new (Function0 ~> Function0ʹ):
      def apply[T](f0: Function0[T]): Function0ʹ[T] =
        as.counter += 1
        new Function0ʹ(f0)
```

Next, instantiate `Algorithms` and use `mapK(Function0ʹ.counting)` on a `Trampoline[Int]` value:

```scala
scala> implicit val as: Algorithms = Algorithms(20, 0)
val as: Algorithms = Algorithms(20,0)

scala> as.fib.mapK(Function0ʹ.counting)
val res1: cats.free.Free[Function0ʹ, Int] = Free(...)

scala> res1.runTailRec
val res2: Function0ʹ[Int] = <function0>

scala> res2()
val res3: Int = 6765

scala> as.counter
val res4: Int = 10946
```

The value of the counter is exactly the number of _base cases_ (which coincides with that of `liftF` invocations).

[Previous](https://github.com/sjbiaga/kittens/blob/main/expr-eert/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/eval-2-expr-tree/README.md)
