[Previous](https://github.com/sjbiaga/kittens/blob/main/expr-07-builder/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-09-ring/README.md)

Lesson 03: A Rich Language of Expressions (cont'd)
==================================================

Exercise 03.1 - Part 1
----------------------

Knowing that `Val(2): Expr[Int]` can always be "inflated" to `Val(Val(2)): Expr[Expr[Int]]`, give a typeclass instance of
the `CoflatMap` typeclass for `Expr`. [Hint: implement the `coflatten` method.]

Solution
--------

Because `CoflatMap` inherits `Functor`, we have to give implementations only for `map` and `coflatten`; then `coflatMap` can
be defined in their terms.

```
def coflatMap[A, B](xa: Expr[A])(f: Expr[A] => B): Expr[B] =
  map(coflatten(xa))(f)
```

We already introduced the value [`kittensExprFunctor`](https://github.com/sjbiaga/kittens/blob/main/expr-03-swap/README.md)
as typeclass instance of the `Functor` typeclass for `Expr`:

```Scala
implicit val kittensExprFunctor: Functor[Expr] =
  new Functor[Expr]:
    def map[A, B](xa: Expr[A])(f: A => B): Expr[B] =
      xa match
        case Val(a)        => Val(f(a)) // line #a
        case Inv(rhs)      => Inv(map(rhs)(f))
        case Add(lhs, rhs) => Add(map(lhs)(f), map(rhs)(f))
        case Sub(lhs, rhs) => Sub(map(lhs)(f), map(rhs)(f))
        case Mul(lhs, rhs) => Mul(map(lhs)(f), map(rhs)(f))
        case Div(lhs, rhs) => Div(map(lhs)(f), map(rhs)(f))
        case it @ ( Zero | One ) => it
```

so only `coflatten` is left for implementation:

```Scala
implicit val kittensExprCoflatMap: CoflatMap[Expr] =
  new CoflatMap[Expr]:
    def map[A, B](xa: Expr[A])(f: A => B): Expr[B] = kittensExprFunctor.map(xa)(f)
    override def coflatten[A](xa: Expr[A]): Expr[Expr[A]] =
      xa match
        case it @ Val(_)       => Val(it) // line #6
        case Inv(rhs)          => Inv(coflatten(rhs))
        case Add(lhs, rhs)     => Add(coflatten(lhs), coflatten(rhs))
        case Sub(lhs, rhs)     => Sub(coflatten(lhs), coflatten(rhs))
        case Mul(lhs, rhs)     => Mul(coflatten(lhs), coflatten(rhs))
        case Div(lhs, rhs)     => Div(coflatten(lhs), coflatten(rhs))
        case it @ (Zero | One) => it
    def coflatMap[A, B](xa: Expr[A])(f: Expr[A] => B): Expr[B] =
      map(coflatten(xa))(f) // line #14
```

We are also given the method `eval: Expr[Int | Double] => Double`, thus, `eval` can be used as function parameter to
`coflatMap` for arguments of type `Eval[Eval[Int]]`:

```Scala
kittensExprCoflatMap.coflatten(Inv(Mul(One, Add(Val(1), Zero))))
kittensExprCoflatMap.coflatMap(Inv(Mul(One, Add(Val(1), Zero))))(eval)
```

It is now obvious that `coflatten` does _not_ change the original `Expr`ession, except for the `Val` case, when it inflates
`Val(1)` into `Val(Val(1))` in line #6. When `eval` is applied in line #14, it will pattern match line #a in
`kittensExprFunctor`, which will bind `a` to `Val(1)`, so, an expression of type `Expr[Int]` - this `eval` knows how to
evaluate.

Note that we cannot evaluate with `eval` a "higher-order" expression of type `Expr[Expr[Int]]`:

```Scala
eval(kittensExprCoflatMap.coflatten(Inv(Mul(One, Add(Val(1), Zero))))) // compile error
```

To give a typeclass instance of the `FlatMap` typeclass for `Expr`,
see [Lesson 06 - Exercise 06.6](https://github.com/sjbiaga/kittens/blob/main/eval-2-expr-tree/README.md) for an implementation
of `flatten`.

Exercise 03.1 - Part 2
----------------------

Give an implementation for evaluating expressions of type `Expr[Double => Double]` downto `Double => Double`.

Solution
--------

These are expressions of function base type, so `Zero` and `One` should map to constant functions: `Function.const(0)`,
respectively, `Function.const(1)`. The return type should be a function, too. The binary operators should map to anonymous
functions, whose parameter being applied as argument to the functions resulting from evaluating the operands, then the
corresponding operation should be performed.

```Scala
def evalʹ(expr: Expr[Double => Double]): unit ?=> (Double => Double) =
  expr match
    case Zero      => Function.const(0d)
    case One       => Function.const(1d)
    case Val(f)    => f
    case Inv(n) if summon[unit] eq Zero => { k => -evalʹ(n).apply(k) }
    case Inv(n) if summon[unit] eq One  => { k => 1d / evalʹ(n).apply(k) }
    case Add(m, n) => { k => evalʹ(m).apply(k) + evalʹ(n).apply(k) }
    case Sub(m, n) => { k => evalʹ(m).apply(k) - evalʹ(n).apply(k) }
    case Mul(m, n) => { k => evalʹ(m).apply(k) * evalʹ(n).apply(k) }
    case Div(m, n) => { k => evalʹ(m).apply(k) / evalʹ(n).apply(k) }
```

Note that `.apply` can be ommitted. Also, the return type of `evalʹ` is a context function type, with `unit` as implicit
parameter, on which `Inv` discriminates whether to negate (additive case) or reciprocate (multiplicative case). Besides
constants `Zero` and `One`, all the other cases are identical in form, lest the operator; except the `Val` case, when the
bound `f` is directly used as a return value.

```scala
scala> given unit = One

scala> kittensExprCoflatMap.coflatten(Inv(Mul(Val((_: Double).+(1)), Add(Val((_: Double).*(0)), Val((_: Double).-(1))))))
val res2: Expr[Expr[Double => Double]] = Inv(Mul(Val(Val(rs$line$20$$$Lambda/0x00007fe53766dfc0@4d4b0e1a)),Add(Val(Val(rs$line$20$$$Lambda/0x00007fe53766e3b0@5c4de465)),Val(Val(rs$line$20$$$Lambda/0x00007fe53766e7a0@36e6ea6c)))))

scala> kittensExprCoflatMap.coflatMap(Inv(Mul(Val((_: Double).+(1)), Add(Val((_: Double).*(0)), Val((_: Double).-(1))))))(evalʹ)
val res3: Expr[Double => Double] = Inv(Mul(Val(rs$line$10$$$Lambda/0x00007f3c43624220@783a8ec4),Add(Val(rs$line$10$$$Lambda/0x00007f3c43625978@34afee7c),Val(rs$line$10$$$Lambda/0x00007f3c43650000@7e632933))))
```

Now, because `Expr` is a functor, we can map the _application function_ with some argument (`_(0d)`) and obtain an
`Expr[Double]` value, which this we can evaluate to a number:

```Scala
scala> res3.map(_(0d))
val res4: Expr[Double] = Inv(Mul(Val(1.0),Add(Val(0.0),Val(-1.0))))

scala> eval(res4)
val res5: Double = -1.0
```

We might have avoided the use of `coflatMap` altogether and straightly rely only on `evalʹ` instead.

```scala
scala> Inv(Mul(Val((_: Double).+(1)), Add(Val((_: Double).*(0)), Val((_: Double).-(1)))))
val res6: Expr[Double => Double] = Inv(Mul(Val(rs$line$9$$$Lambda/0x00007f504b6613d8@6467ce1a),Add(Val(rs$line$9$$$Lambda/0x00007f504b6617c8@5637ed9d),Val(rs$line$9$$$Lambda/0x00007f504b661bb8@45174eba))))

scala> evalʹ(res6)
val res7: Double => Double = Lambda/0x00007f504b6a6000@2c8542d4

scala> res7(0d)
val res8: Double = -1.0
```

[Previous](https://github.com/sjbiaga/kittens/blob/main/expr-07-builder/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-09-ring/README.md)
