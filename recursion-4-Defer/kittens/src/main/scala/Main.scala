import cats.{ Defer, Eval }

object Main:

  val factorial: Long => Eval[Long] = Defer[Eval].recursiveFn {
    fac => {
      n =>
        if n <= 0
        then
          Eval.now(1L)
        else
          for
            k <- fac(n-1)
          yield
            n * k
    }
  }

  val fibonacci: Long => Eval[Long] = Defer[Eval].recursiveFn {
    fib => {
      n =>
        if n <= 1
        then
          Eval.now(1L min (0L max n))
        else
          for
            p <- fib(n-1)
            q <- fib(n-2)
          yield
            p + q
    }
  }

  def main(args: Array[String]): Unit =
    println {
      factorial(5).value
    }
    println {
      fibonacci(5).value
    }
