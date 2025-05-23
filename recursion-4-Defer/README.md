[First](https://github.com/sjbiaga/kittens/blob/main/recursion-1-lambda-calculus/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/recursion-3-Cofree/README.md)

Lesson 09 - Recursion (cont'd)
==============================

The `Defer[F[_]]` trait revolves around the method:

```Scala
def defer[A](fa: => F[A]): F[A]
```

The fact that the parameter is call-by-name _must_ be preserved in the result, for example, in a `lazy` `val`ue, or as a
`Function0`, but at the same time note that the type of the result is the same with the parameter: this observation may be
pertinent depending on whether a typeclass instance of `Defer` is given, or this trait is inherited; in the former case,
there may be some _`case class`_ inheriting a `sealed` trait that can handle the call-by-name parameter, while in the latter
case, the call-by-name parameter may be passed to another handling _method_ in the same type.

It is a typeclass with typeclass instances such as `Defer[Eval]` (via `Eval.defer`), `Defer[Free[S, *]]` (via `Free.defer`),
`Defer[TailRec]` (via Scala's `Tailrec.tailcall`), `Defer[Function1[A, *]]`, or `Defer[Function0]`, and of the most
monad transformers - but through an `implicit` `F: Defer[F]`:

1. [`Defer[EitherT[F, L, *]]`](https://github.com/sjbiaga/kittens/blob/main/mt-2-EitherT/README.md#typeclass-instances)

1. [`Defer[OptionT[F, *]]`](https://github.com/sjbiaga/kittens/blob/main/mt-3-OptionT/README.md#typeclass-instances)

1. [`Defer[IorT[F, E, *]]`](https://github.com/sjbiaga/kittens/blob/main/mt-4-IorT/README.md#typeclass-instances)

1. [`Defer[Kleisli[F, A, *]]`](https://github.com/sjbiaga/kittens/blob/main/mt-5-ReaderT/README.md#typeclass-instances)

1. [`Defer[IndexedStateT[F, SA, SB, *]]`](https://github.com/sjbiaga/kittens/blob/main/mt-7-StateT/README.md#typeclass-instances)

1. [`Defer[WriterT[F, L, *]]`](https://github.com/sjbiaga/kittens/blob/main/mt-6-WriterT/README.md#typeclass-instances)

It is also inherited by `cats.effect.kernel.Sync[F[_]]` (and indirectly used with `IO` monad as type argument instead of `F`):

```Scala
trait Sync[F[_]] extends MonadCancel[F, Throwable] with ... with Defer[F] {
  def defer[A](thunk: => F[A]): F[A] =
    flatten(delay(thunk))
  def delay[A](thunk: => A): F[A] =
    suspend(Sync.Type.Delay)(thunk)
  def suspend[A](hint: Sync.Type)(thunk: => A): F[A]
}
```

---

The `Defer[F[_]]` trait defines also a convenience `fix`point combinator method:

```Scala
def fix[A](fn: F[A] => F[A]): F[A] = {
  lazy val self: F[A] = fn { // line #a
    defer(self)              // line #b
  }
  self                       // line #c
}
```

(to quote:

    Defer instances, like functions, parsers, generators, IO, etc...
    often are used in recursive settings where this function is useful)

where type `F[A]` wraps _somehow_ an `S => T` function type (maybe `T => T`), while the function parameter `fn` knows how to
unwrap a _function_ `S => T` from its argument, then _create_ a function that takes an argument `S` and _applies_ the former
function a certain number of times - hence, it invokes itself recursively -, possibly _conditioned_ and with the _argument_
involved (or not) in larger _expressions_; finally, the latter function is wrapped as `F[A]`.

We illustrate an example using either the `Defer[[T] =>> Function1[Int, T]]` or the `Defer[Eval]` typeclass instance. The
recursive function is of type `Int => Int`, and it invokes itself recursively by subtracting `4` from its argument. We
present both an infinite recursive variant - which raises the `StackOverflowError` exception -, as well as a finite variant.

1. For the `Function1[Int, *]` type constructor with a context, we give the following excerpt from a `REPL` session:

```scala
scala> imports cats.Defer, cats.instances.function._

scala> Defer[[T] =>> Function1[Int, T]].fix[Int] { (m: Int => Int) => { (n: Int) => m(n-4) } }  // infinite recursion
val res0: Int => Int = Lambda$1860/0x00007f13d861e1c8@4fa4b57f

scala> res0(7)
java.lang.StackOverflowError

scala> Defer[[T] =>> Function1[Int, T]].fix[Int] { (m: Int => Int) => { (n: Int) => if n <= 0 then n else m(n-4) } }
val res2: Int => Int = Lambda$1862/0x00007f13d861f1a8@776c147d

scala> res2(7)
val res3: Int = -1
```

We observe that `m` is the function parameter to -, while `{ (n: Int) => ... m(n-4) ... }` is the result of - `fn`.

In the cases of `res0` and `res2`, the `self` `lazy` `val`ue has type `Int => Int`. The following snippet instantiates a
typeclass of `Defer` for the `Function1[S, *]` context:

```Scala
new Defer[S => *] {
  case class Deferred[T](fa: () => S => T) extends (S => T) {
    private lazy val resolved: S => T = ???
    def apply(a: S): T = resolved(a)       // line #13
  }
  def defer[T](fa: => S => T): S => T = {  // line #15
    lazy val cachedFa = fa                 // line #16
    Deferred(() => cachedFa)               // line #17
  }
}
```

So here `S` and `T` are both `Int`. The `defer` method from lines #15-#17 is passed an `fa` call-by-name expression denoting
a function; caching it in line #16 means only that it will be evaluated once, for the first time only (otherwise, the
expression - though unlikely for functional expressions - might have been evaluated each time it were used). In line #17, the
method instantiates a nested class `Deferred` from `cachedFa`, with a parameter - a `Function0` of type `Function1[S, T]`.

Now, this nested class extends `(S => T)`, so its instance can be used as result of `defer`. However, only in line #c, the
`lazy` `val`ue `self` is evaluated, and in order to evaluate it, the right hand side in line #a says that the `defer(self)`
in line #b must be passed as argument to `fn`. Yet, `self` has _not_ been evaluated, but it may serve as the _call-by-name_
parameter in line #15.

The result from line #17 is but evaluated: an instance of the nested class `Deferred` and thus a `Function1[Int, Int]`.
Applying `fn` on this latter "object-function" value will return another function `{ (n: Int) => ... m(n-4) ... }` where `m`
has been captured.

After all this, and after line #c, the value of the `lazy` `val`ue `self` is initialized. This is either `res0` or `res2`.
Nevertheless, in both these cases, the captured `m` lurks still unapplied, though its delayed application will result in the
very function in which it "occurs it`self` recursively": then, `self` and `m` will reference _the same_ "object-function"
value.

Both `res0` and `res2` only have the potential of being applied, and it is during application, that the delayed application
takes place. So, in the case of `res0`, applying `res0(7)` - which happens in llne #13 just after `resolved` returns - will
make `self` call itself recursively ad infinitum - hence, the `StackOverflowError` exception.

In the case of `res2`, applying `res2(7)` - idem -, also `self` will invoke itself recursively, but this time the parameter
`n` will be compared with `0`, and recursion will stop when `n` equals `-1`.

Note how the parameter to `fix` is `Int` (not a function), but `F[A]` results as `Function1[Int, Int]`, which _is_ a function.

2. For the `Eval` type constructor, we give the following excerpt from a `REPL` session:

```scala
scala> imports cats._

scala> def m(f: Eval[Int => Int]): Eval[Int => Int] = Eval.now { n => f.value(n-4) }
def m(f: cats.Eval[Int => Int]): cats.Eval[Int => Int]

scala> Defer[Eval].fix[Int => Int](m)
val res4: cats.Eval[Int => Int] = cats.Later@5c623ff7

scala> res4.value(7)
java.lang.StackOverflowError

scala> def m(f: Eval[Int => Int]): Eval[Int => Int] = Eval.now { n => if n <= 0 then n else f.value(n-4) }
def m(f: cats.Eval[Int => Int]): cats.Eval[Int => Int]

scala> Defer[Eval].fix[Int => Int](m)
val res6: cats.Eval[Int => Int] = cats.Later@7ea616b3

scala> res6.value(7)
val res7: Int = -1
```

`m: Eval[Int => Int] => Eval[Int => Int]` is a function that is passed as the function parameter `fn` to `fix`, this time
defined - straighter - as part of the typeclass instance `Defer[Eval]`:

```Scala
new Defer[Eval] {
  def defer[A](e: => Eval[A]): Eval[A] =
    Eval.defer(e)
}
```

To evaluate `self` in line #c is to apply the parameter `fn` (argument `m`) at line #a to `defer(self)` from line #b: as
before, an `Eval.Defer` instance will hold a computation not evaluated that results in `self`; after these steps, `self`
becomes evaluated, but it also lurks as a `Function0` unapplied in the `Eval.Defer[Int => Int]`. When `fn` is applied to the
latter, the function `m` will return an `Eval[Int => Int]` that captured the latter as `f`; and when `f.value` is invoked,
the `Eval.Defer[Int => Int]` will yield `self` from line #c.

As before, `res4.value(7)` will overflow the stack, whereas `res6.value(7)` will return `-1`.

The purpose of `defer` is manifest: keep a `Function0` unapplied until after `self` will have been initialized, and apply it
to reference the same object-function as `self`. The former is captured in it`self`, while the latter (`self`) is returned to
the caller of `fix`. However, this method does not provide for stack safety.

---

Another similar method related to recursion in `Defer` is `recursiveFn`:

```Scala
def recursiveFn[A, B](fn: (A => F[B]) => (A => F[B])): A => F[B] =
  new Function1[A, F[B]] {
    val self: A => F[B] = fn(this)          // line #3

    def apply(a: A): F[B] = defer(self(a))  // line #5
  }
```

and here too the `defer` method has its role. The higher-order function parameter `fn` is defined such that the (name of the)
_first_ function argument (of type `A => F[B]`) occurs in the result (of the same type), which is another function with an
argument that the aforementioned function can be applied to.

The `recursiveFn` method returns an object-function, whose `apply` method delegates indirectly to a member field `self`, via
the `defer` method (line #5). Thus, the returned object-function is an _alias_ of `self`: applying the alias to an `a: A`
applies the member field (`self`) to the same argument `a: A`. In line #3, however, the occurrences of the name from `fn` are
bound to `this`, to the alias (and it could not have been otherwise). So, the alias of `self` is scattered to invoke it`self`
recursively, albeit indirectly.

Before we discuss the role of the `defer` method, let us define a top-level method `recursiveFnʹ` without a `Defer` involved:

```Scala
def recursiveFnʹ[F[_], A, B](fn: (A => F[B]) => (A => F[B])): A => F[B] =
  new Function1[A, F[B]] {
    def apply(a: A): F[B] = fn(this).apply(a)
  }
```

and also work with two examples - but the same factorial function -, one using the typeclass instance of `Defer` for `Eval`:

```Scala
val factorial: Long => Eval[Long] = Defer[Eval].recursiveFn {
  fac => {
    n =>
      if n <= 0
      then
        Eval.now(1L)
      else
        Eval.later(n * fac(n-1).value)
  }
}
```

and another using the top-level method `recursiveFnʹ`:

```Scala
val factorialʹ: Long => Eval[Long] = recursiveFnʹ {
  fac => {
    n =>
      if n <= 0
      then
        Eval.now(1L)
      else
        Eval.later(n * fac(n-1).value)
  }
}
```

Surprisingly perhaps, invoking either of these two factorial functions with a large argument (`10000`) will raise the
`StackOverflowError` exception. But let us modify the two factorials using a stack safe implementation:

```Scala
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
```

respectively:

```Scala
val factorialʹ: Long => Eval[Long] = recursiveFnʹ {
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
```

Now, only `factorialʹ` will raise the `StackOverflowError` exception when invoked with a large argument (`10000`). Let us try
to alter further this function:

```Scala
val factorialʹʹ: Long => Eval[Long] = recursiveFnʹ {
  fac => {
    n =>
      if n <= 0
      then
        Eval.now(1L)
      else
        for
          _ <- Eval.Unit
          k <- fac(n-1)
        yield
          n * k
  }
}
```

Neither `factorialʹʹ` will raise the `StackOverflowError` exception any longer when invoked with a large argument (`10000`)!

Thus, we may conclude that using the `defer` method in line #5 provides with stack safety (as it is not necessary to commence
the `for`-comprehension with `_ <- Eval.Unit`). However, this is not necessarily so: the `Defer[[T] =>> Function1[Int, T]]`
typeclass instance is not stack safe, as the following example illustrates:

```Scala
val factorialʹʹʹ: Long => Function1[Long, Long] = Defer[[T] =>> Function1[Long, T]].recursiveFn {
  fac => {
    n =>
      if n <= 0
      then
        identity
      else
        for
          _ <- Monad[[T] =>> Function1[Long, T]].unit
          k <- fac(n-1)
        yield
          n * k
  }
}
```

because the `Monad[[T] =>> Function1[Long, T]]` typeclass instance is not stack safe, in turn. For, try to invoke:

```scala
scala> factorialʹʹʹ(10000)(1)
java.lang.StackOverflowError
```

and it will raise a `StackOverflowError` exception.

Besides `factorial`, we can also implement `fibonacci` using the `recursiveFn` method of the `Defer[Eval]` typeclass instance:

```Scala
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
```

### [`ContT`](https://typelevel.org/cats/datatypes/contt.html)

`ContT` is a [CPS](https://en.wikipedia.org/wiki/Continuation-passing_style) monad; it is based on `Defer`, or, to quote, it

    leverage[s] the Defer type class to obtain stack-safety.

A `ContT`inuation is a `sealed` parameterized type with just two derived `case class`es: `FromFn` and `DeferCont`; it has
three type parameters - the first of which is a context `M[_]` -, and a (`final`) method `run: (B => M[A]) => M[A]`:

```Scala
package cats
package data

sealed abstract class ContT[M[_], A, +B] extends Serializable {
  final def run: (B => M[A]) => M[A] = runAndThen
  protected def runAndThen: AndThen[B => M[A], M[A]]
  ...
}

object ContT {
  private case class FromFn[M[_], A, B](runAndThen: AndThen[B => M[A], M[A]]) extends ContT[M, A, B]

  private case class DeferCont[M[_], A, B](next: () => ContT[M, A, B]) extends ContT[M, A, B] {
    @annotation.tailrec
    private def loop(n: () => ContT[M, A, B]): ContT[M, A, B] =
      n() match {
        case DeferCont(n) => loop(n)
        case notDefer     => notDefer
      }

    protected lazy val runAndThen: AndThen[B => M[A], M[A]] = loop(next).runAndThen
  }

  ...
}
```

(`AndThen` is in turn a `sealed` parameterized type:

```Scala
sealed abstract class AndThen[-T, +R] extends (T => R) ... { ... }
```

which is thus a `Function1`, but used to optimize many compositions with `andThen` or `compose`.)

Thus, both `map` and `flatMap` methods prompt for an `implicit` typeclass instance of the `Defer` typeclass for `M`. It is
the third type parameter (`B`) that can vary with `map` and `flatMap`, while the second type parameter (`A`) remains constant
throughout.

In the `ContT.apply` method:

```Scala
object ContT {
  def apply[M[_], A, B](fn: (B => M[A]) => M[A]): ContT[M, A, B] =
    FromFn(AndThen(fn))
}
```

the `fn` parameter is a _higher-order function_, which takes as arguments _callback_s. At some call sites of `ContT.apply`,
this parameter is just an anonymous function, because when the value `B` is already known, "applying" a placeholder - standing
for the callback - to a `B`, forms the (anonymous) function `(B => M[A]) => M[A]`.

We can illustrate this on the `ContT.defer` method from the companion object:

```Scala
object ContT {
  def defer[M[_], A, B](b: => B): ContT[M, A, B] =
    apply(_(b))
}
```

where `_(b)` stands for the function literal `{ (cb: B => M[A]) => cb(b): M[A] }: (B => M[A]) => M[A]`.

However, in either the `map` or the `flatMap` method, at the call site of `ContT.apply`, the callback (`cbʹ`) parameter is
used in _compositions_ with other functions, hence it is _not_ applied to a `Bʹ`:

```Scala
final def map[Bʹ](fn: B => Bʹ)(implicit M: Defer[M]): ContT[M, A, Bʹ] = {
  val fnAndThen = AndThen(fn)
  ContT.apply { cbʹ =>
    val cb = fnAndThen.andThen(cbʹ)                   // line #04
    M.defer(this.run(cb))                             // line #05
  }
}
final def flatMap[Bʹ](fn: B => ContT[M, A, Bʹ])(implicit M: Defer[M]): ContT[M, A, Bʹ] = {
  val fnAndThen = AndThen(fn)
  ContT.apply { cbʹ =>
    val contRun: ContT[M, A, Bʹ] => M[A] = { self =>  // line #11
      M.defer(self.run(cbʹ))                          // line #12
    }
    val cb = fnAndThen.andThen(contRun)               // line #14
    M.defer(this.run(cb))                             // line #15
  }
}
```

Thus, when creating `ContT`inuation objects through either `map` or `flatMap`, the callbacks are not applied to, only composed
with; it is only via the `ContT.pure`, `ContT.defer`, or `ContT.liftF` methods in the companion object that the resulting
`ContT`inuations virtually apply callbacks to arguments. Thus, the `ContT`inuation result of a `for`-comprehension need only
be passed a callback (_not_ its argument), and it takes over from there, downto an `M[A]`.

Note that both the companion class methods and the companion object methods, wrap their function parameters in `AndThen`, so
we would expect these `AndThen` objects to concatenate - lines #04 and #14.

Also about `for`-comprehensions - translated by Scala as nesting `flatMap`s -, or chaining `flatMap`s one after another, we
know that each `flatMap` method has the same return type as any other. And that the evaluation is outer-to-inner (or
top-to-bottom if nesting), left-to-right if chaining.

---

Let us take nesting `flatMap`s for illustration (for edification, look at the [exercise](#solution---part-3) below). We will
see how the very same callback that the `ContT#run` method is invoked with - by user code -, is passed down to the innermost
`ContT`inuation unchanged.

The top _receiver_ of the outer `flatMap` is a `ContT`inuation which knows how to apply a callback to its argument. Invoking
`flatMap` on this receiver, builds - with the `flatMap`'s function parameter - and returns another `ContT`inuation. Invoking
`run` on the latter - by user code -, will pass it a callback, which it knows to pass it further to the _result_ of -, and in
the eventuality of -, the function parameter of `flatMap` being invoked: all that was said enters the composition of a second
callback - line #14 -, that `this.run` method is applied to (where `this` is the former top receiver) - line #15: well,
wrapped in an `M.defer`, thus not immediately applicable, and hence, stack safe.

Now, the second callback is applied to the argument available in the former `ContT`inuation. The first thing that the invoked
function (callback) does is to apply the function parameter of (the outer) `flatMap` to the said argument. This yields a
`ContT`inuation - call it `self` -, which is nested in the outer `flatMap`. Yet, this nested `ContT`inuation is the result of
applying an inner `flatMap` to a receiver (with an available argument) too. [It is possible that the receiver results from
applying some function to the argument passed to the function parameter of the outer `flatMap`.]

We are in the eventuality that the function parameter of the outer `flatMap` would be invoked. But this was composed - with
`contRun` from lines #11-#12 - in line #14. Applying `self.run` to the actual (initial) callback passed by user code, is thus
the second thing which occurs: well, wrapped in an `M.defer`, thus not immediately applicable, and hence, stack safe. But
this just means that the whole discussion is repeated.

Eventually, the `for`-comprehension invokes `map`, which builds - with the `map`'s function parameter - and returns another
`ContT`inuation - line #04 -, call it `self`. Having been invoked by the call to `self.run` method in line #12, `self` will
be passed the initial callback passed by user code. After first applying the function parameter to `map`, thus obtaining the
`Bʹ` result of the `for`-comprehension, the second thing is to apply it the callback, which _always_ yields an `M[A]` (type
`A` is invariable).

Thus, there must be some connection between `Bʹ` and `A`: if they are the same, `ContT#eval` can be used by user code instead
of `ContT#run`, to pass an unspecified initial callback.

---

Whether `map` or `flatMap`, the lines #04-#05 and lines #14-#15 look very similar; and in the `flatMap` method, line #12 is
similar to line #15: it is just the receiver which differs, `self`, respectively, `this`. In the `map` method, in line #04,
the real callback to `this.run` is formed by composing the wrapped argument `fn` and the actual `cbʹ` that will be invoked
after performing `map`. Whereas in the `flatMap` method, the wrapped parameter function `fn: B => ContT[M, A, Bʹ]` and the
function `val`ue `contRun: ContT[M, A, Bʹ] => M[A]` from lines #11-#12, can be composed into a function `cb: B => M[A]` in
line #14.

In fact, line #14 might have been written as line #14ʹ:

```Scala
val cb = fn.andThen(_.run(cbʹ))  // line #14ʹ
```

without wrapping `fn` or `M.defer`ring. However, wrapping in `AndThen` optimizes, while the typeclass instance `Defer[M]`
provides for stack safety.

Let us look at an example, the `factorial` function, implemented with `for`-comprehensions of `ContT`inuation type:

```Scala
def factorial(n: Long): Long =
  def factorialʹ(n: Long, f: Long): ContT[Eval, Long, Long] =
    for
      b <- ContT.defer(n == 0)
      r <- ( if b
             then
               ContT.pure(f)
             else
               for
                 m <- ContT.defer(n - 1)
                 p <- ContT.defer(n * f)
                 r <- factorialʹ(m, p)
               yield
                 r
           )
    yield
      r
  factorialʹ(n, 1).eval.value
```

The nested `factorialʹ` method has a second parameter "`f`" which stores the partial result, and has as the return type
`ContT[Eval, Long, Long]`. Because of that, the `ContT#eval` can be used to trigger the stack safe computation which results
in an `Eval[Long]`. Although the "`else`" branch could have been written - more direct - as `factorialʹ(n - 1, n * f)`, each
computation is wrapped in a `ContT.defer`. The "recursive" invocation of `factorialʹ` is stack safe because it is wrapped in
an `Eval.defer`.

Exercise 09.4
-------------

Using `Expr`essions
[parser](https://github.com/sjbiaga/kittens/blob/main/expr-05-parser/README.md#an-expression-parser-contd),
[builder](https://github.com/sjbiaga/kittens/tree/main/expr-07-builder#an-expression-builder-contd),
[simplifier](https://github.com/sjbiaga/kittens/blob/main/expr-simplify/README.md#solution), and
[evaluator](https://github.com/sjbiaga/kittens/tree/main/expr-02-eval#evaluation-of-expressions) from previous lessons or
exercises, define at least two continuation builders (`builderContT` and `builderContTʹ`), a continuation simplifier
(`simplifyContT`), a continuation evaluator (`evalContT`), and a "division by zero" continuation checker (`divByZeroContT`),
then intercalate them:

```Scala
val c: ContT[Eval, Expr[Double], Double] =
  for
    x <- ContT.defer(Inv(x"(1.0-0.0) * (1.0+0.0)"))
    xʹ = x.asInstanceOf[Expr[Double]]
    x <- builderContT(xʹ)
    x <- simplifyContT(x)
    x <- builderContTʹ(x)
    x <- simplifyContT(x)
    d <- evalContT(x)
    s <- divByZeroContT(d)
    _ <- ContT.defer(println(s))
  yield
    d
```

so as to obain a `Double` starting from an `Expr[Double]`. Also, translate the `for`-comprehension to nesting `flatMap`s, as
well as illustrate chaining `flatMap`s.

[Hint: use `Defer[Eval]` as the typeclass instance of the `Defer` typeclass, and run the `c` continuation with:

```Scala
println {
  c.run(Val.apply[Double] andThen Eval.later).value
}
```

and define each `ContT`inuation (involving `Expr`essions) as a function `Expr[Double] => ContT[Eval, Expr[Double], T]`, where
the type `T` is `Double` for `evalContT`, and `Expr[Double]` for the rest. The type of the `divByZeroContT` `ContT`inuation
would be `Double => ContT[Eval, Expr[Double], String]`.

Try to use `ContT.pure` or `ContT.defer` instead of `ContT.apply`.]

Solution - Part 1
-----------------

We define `Expr`essions, their parser, interpolator, evaluator, builder, and simplifier, as follows:

```Scala
import scala.util.control.TailCalls._
import scala.util.parsing.combinator.JavaTokenParsers

import alleycats.{ Zero => `0`, One => `1` }

import cats.~>

enum Expr[+T]:
  case Add[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case Sub[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case Zero extends Expr[Nothing]
  case Mul[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case Div[+T](lhs: Expr[T], rhs: Expr[T]) extends Expr[T]
  case One extends Expr[Nothing]
  case Inv[+T](rhs: Expr[T]) extends Expr[T]
  case Val[T](n: T) extends Expr[T]

object Expr extends JavaTokenParsers:

  type unit = Expr.Zero.type | Expr.One.type

  def expr(implicit unit: unit): Parser[Expr[Int | Double]] =
    term ~ rep(("+"|"-") ~ term) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "+" ~ rhs) => Add(lhs, rhs)
        case (lhs, "-" ~ rhs) => Sub(lhs, rhs)
      }
    }

  def term(implicit unit: unit): Parser[Expr[Int | Double]] =
    factor ~ rep(("*"|"/") ~ factor) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "*" ~ rhs) => Mul(lhs, rhs)
        case (lhs, "/" ~ rhs) => Div(lhs, rhs)
      }
    }

  def factor(implicit unit: unit): Parser[Expr[Int | Double]] =
    ("+"|"-") ~ literal ^^ {
      case "-" ~ rhs if unit eq Zero => Inv(rhs)
      case "+" ~ rhs => Add(Zero, rhs)
      case "-" ~ rhs => Sub(Zero, rhs)
    } |
    literal ^^ { identity }

  def literal(implicit unit: unit): Parser[Expr[Int | Double]] =
    floatingPointNumber ^^ { it =>
      it.toDouble match
        case 0d => Zero
        case 1d => One
        case n => Val(n)
    } |
    decimalNumber ^^ { it =>
      it.toInt match
        case 0 => Zero
        case 1 => One
        case n => Val(n)
    } |
    "("~> expr <~")" ^^ { identity }

  implicit class ExprInterpolator(private val sc: StringContext) extends AnyVal:
    def x(args: Any*)(implicit unit: unit): Expr[Int | Double] =
      val inp = (sc.parts zip (args :+ "")).foldLeft("") {
        case (r, (p, a)) => r + p + a
      }
      parseAll(expr, inp) match
        case Success(it, _) => it

  def eval(expr: Expr[Double])(implicit unit: unit, `0`: `0`[Double], `1`: `1`[Double]): Double =
    def evalʹ(xa: Expr[Double]): TailRec[Double] =
      xa match
        case Zero => done(`0`.zero)
        case One => done(`1`.one)
        case Val(n) => done(n)
        case Inv(xn) if Zero eq unit =>
          for
            n <- tailcall { evalʹ(xn) }
          yield
            `0`.zero - n
        case Inv(xn) if One eq unit =>
          for
            n <- tailcall { evalʹ(xn) }
          yield
            `1`.one / n
        case Add(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            m + n
        case Sub(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            m - n
        case Mul(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            m * n
        case Div(xm, xn)       =>
          for
            m <- tailcall { evalʹ(xm) }
            n <- tailcall { evalʹ(xn) }
          yield
            m / n
    evalʹ(expr).result

  val swap: unit ?=> Expr ~> Expr =
    new (Expr ~> Expr):
      def apply[T](expr: Expr[T]): Expr[T] =
        def applyʹ(xa: Expr[T]): TailRec[Expr[T]] =
          xa match
            case Zero        => done(One)
            case One         => done(Zero)
            case Add(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Mul(m, n)
            case Sub(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Div(m, n)
            case Mul(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Add(m, n)
            case Div(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                Sub(m, n)
            case Inv(Zero)
              if summon[unit] eq One => applyʹ(Div(One, Zero))
            case Inv(xn)     =>
              for
                n <- tailcall { applyʹ(xn) }
              yield
                Inv(n)
            case it          => done(it)
        applyʹ(expr).result

  final case class Builder[T](lhs: Expr[T], private var save: List[Expr[T]]):
    def fill(n: Int)(rhs: Expr[T]) = List.fill(0 max n)(rhs)
    def swapping(implicit unit: unit) = Builder(swap(lhs), save)
    def add(rhs: Expr[T], n: Int = 1) = Builder(fill(n)(rhs).foldLeft(lhs)(Add(_, _)), save)
    def subtract(rhs: Expr[T], n: Int = 1) = Builder(fill(n)(rhs).foldLeft(lhs)(Sub(_, _)), save)
    def multiply(rhs: Expr[T], n: Int = 1) = Builder(fill(n)(rhs).foldLeft(lhs)(Mul(_, _)), save)
    def divide(rhs: Expr[T], n: Int = 1) = Builder(fill(n)(rhs).foldLeft(lhs)(Div(_, _)), save)
    def invert(n: Int = 1): Builder[T] = Builder(List.fill(0 max n)(()).foldLeft(lhs) { (lhs, _) => Inv(lhs) }, save)
    def open = Builder.From(lhs :: save)
    def close(f: (Builder[T], Expr[T]) => Builder[T], invert: Int = 0) =
      val self = Builder(save.head, save.tail)
      f(self, lhs).invert(invert)
  object Builder:
    def start[T] = From[T](Nil)
    final case class From[T](save: List[Expr[T]]):
      def apply(lhs: Expr[T]): Builder[T] = Builder(lhs, save)

  val simplify: unit ?=> Expr ~> Expr =
    new (Expr ~> Expr):
      val unit = summon[unit]
      def apply[T](expr: Expr[T]): Expr[T] =
        def applyʹ(xa: Expr[T]): TailRec[Expr[T]] =
          xa match
            case Add(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                if n eq Zero then m
                else if m eq Zero then n
                else Add(m, n)
            case Sub(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                if n eq Zero then m
                else if (m eq Zero) && (unit eq Zero) then Inv(n)
                else Sub(m, n)
            case Mul(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                if n eq One then m
                else if m eq One then n
                else if (n eq Zero) || (m eq Zero) then Zero
                else Mul(m, n)
            case Div(xm, xn) =>
              for
                m <- tailcall { applyʹ(xm) }
                n <- tailcall { applyʹ(xn) }
              yield
                if n eq One then m
                else if (m eq One) && (unit eq One) then Inv(n)
                else if m eq Zero then Zero
                else Div(m, n)
            case Inv(xn)     =>
              for
                n <- tailcall { applyʹ(xn) }
              yield
                Inv(n)
            case it          => done(it)
        applyʹ(expr).result
```

Solution - Part 2
-----------------

The `ContT`inuations are the results of the following smart function values (method):

```Scala
given unit = Zero // One

given `0`[Double] = `0`(0d)
given `1`[Double] = `1`(1d)

val builderContT: Expr[Double] => ContT[Eval, Expr[Double], Expr[Double]] =
  xa => ContT.defer {
    Builder.start(xa)
    .add(One)
    .multiply(Val(5d), 4)
      .open(One)
      .add(One, 2)
      .close(_.add(_))
    .swapping
    .lhs
  }

val builderContTʹ: Expr[Double] => ContT[Eval, Expr[Double], Expr[Double]] =
  xa => ContT.defer {
    Builder.start(xa)
    .add(One)
    .multiply(Val(5d), 4)
      .open(One)
      .add(One, 4)
        .open(One)
        .add(One, 5)
          .open(One)
          .add(One, 6)
          .invert(2)
          .close(_.add(_, 2), 4)
        .close(_.add(_), 3)
      .close(_.add(_), 2)
    .swapping
    .lhs
  }

def simplifyContT[A]: Expr[A] => ContT[Eval, Expr[A], Expr[A]] =
  simplify[A] andThen ContT.defer

val evalContT: Expr[Double] => ContT[Eval, Expr[Double], Double] =
  eval andThen ContT.defer
```

Defining the `divByZeroContT` `ContT`inuation to only map to an error message, we can use the following `for`-comprehension
to intercalate the `ContT`inuations:

```Scala
val divByZeroContT: Double => ContT[Eval, Expr[Double], String] =
  d => ContT.defer {
    if d == Double.PositiveInfinity || d == Double.NegativeInfinity
    then
      "Division by zero"
    else
      "No errors"
  }

val c: ContT[Eval, Expr[Double], Double] =
  for
    x <- ContT.defer(Inv(x"(1.0-0.0) * (1.0+0.0)"))
    xʹ = x.asInstanceOf[Expr[Double]]
    x <- builderContT(xʹ)
    x <- simplifyContT(x)
    x <- builderContTʹ(x)
    x <- simplifyContT(x)
    d <- evalContT(x)
    s <- divByZeroContT(d)
    _ <- ContT.defer(println(s))
  yield
    d

println {
  c.run(Val.apply[Double] andThen Eval.later).value
}
```

Solution - Part 3
-----------------

Using a `divByZeroContTʹ` (prime) `ContT`inuation:

```Scala
val divByZeroContTʹ: Double => ContT[Eval, Expr[Double], Double] =
  d => ContT.defer {
    if d == Double.PositiveInfinity || d == Double.NegativeInfinity
    then
      println("Division by zero")
      d
    else
      d
  }
```

where `println`ing the `Division by zero` error message is a side-effect, and which repeats its input as output, we present
the translation of the `for`-comprehension:

```Scala
println { // nesting
  ContT
    .defer(Inv(x"(1.0-0.0) * (1.0+0.0)"))
    .flatMap { x =>
      val xʹ = x.asInstanceOf[Expr[Double]]
      builderContT(xʹ).flatMap {
        simplifyContT(_).flatMap {
          builderContTʹ(_).flatMap {
            simplifyContT(_).flatMap {
              evalContT(_).flatMap {
                divByZeroContTʹ(_).map(identity)
              }
            }
          }
        }
      }
    }.run(Val.apply[Double] andThen Eval.later).value
}
```

as well as, neater, we illustrate the chaining of the (uncluttered) `flatMap` syntax operator `>>=`:

```Scala
println { // chaining
  import cats.syntax.flatMap._
  {
    ContT.defer(Inv(x"(1.0-0.0) * (1.0+0.0)").asInstanceOf[Expr[Double]])
    >>= builderContT
    >>= simplifyContT
    >>= builderContTʹ
    >>= simplifyContT
    >>= evalContT
    >>= divByZeroContTʹ
  }.run(Val.apply[Double] andThen Eval.later).value
}
```

[First](https://github.com/sjbiaga/kittens/blob/main/recursion-1-lambda-calculus/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/recursion-3-Cofree/README.md)
