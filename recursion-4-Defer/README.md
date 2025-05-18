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
in line #b must be passed as argument to `fn`. Yet, `self` has _not_ been evaluated, but it may serve for the _call-by-name_
parameter in line #15.

The result from line #17 is but evaluated: an instance of the nested class `Deferred` and thus a `Function1[Int, Int]`.
Applying `fn` on this latter "object-function" value will return another function `{ (n: Int) => ... m(n-4) ... }` where `m`
has been captured.

After all this, and after line #c, the value of the `lazy` `val`ue `self` is initialized. This is either `res0` or `res2`.
Nevertheless, in both these cases, the captured `m` lurks still unapplied, though its delayed application will result in the
very function in which it "occurs it`self` recursively": then, `self` and `m` will be the same "object-function" value.

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
to be the same object-function as `self`. The former is captured in it`self`, while the latter (`self`) is returned to the
caller of `fix`. However, this method does not provide for stack safety.

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

[First](https://github.com/sjbiaga/kittens/blob/main/recursion-1-lambda-calculus/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/recursion-3-Cofree/README.md)
