[Previous](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/recursion-2-schemes/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/recursion-4-Defer/README.md)

Lesson 09 - Recursion
=====================

Lambda Calculus (fast track)
----------------------------

The BNF grammar has the _lexical_ category of _variables_ - ranged over by `a, b, ..., x, y, ...` -, and the _production_ of
(lambda) terms - ranged over by `A, B, ..., M, N, ...`:

    M ::= x | λ x . M | ( M M )

A term `M N P` is parsed as `((M N) P)`, while a term `λx.λy. M` means `λx. (λy. M)`.

We can encode the boolean constants `true` and `false`, the conditional `if ... then ... else ...`, and the boolean operators
`and` and `or`:

    true := λx.λy.x
    false := λx.λy.y

    if C then M else N := (C M) N

    and C D := λx.λy. if C then (if D then x else y) else y
            := λx.λy. (C (if D then x else y)) y
            := λx.λy. (C ((D x) y)) y

    or C D := λx.λy. if C then x else (if D then x else y)
           := λx.λy. (C x) (if D then x else y)
           := λx.λy. (C x) ((D x) y)

Zero [can](https://en.wikipedia.org/wiki/Lambda_calculus#Arithmetic_in_lambda_calculus) be encoded:

    0 := λf.λx. x

The _successor_ and _predecessor_ can be encoded too, and by the former, the positive natural numbers:

    succ := λn.λf.λx. f (n f x)
    pred := λn.λf.λx. n (λg.λh. h (g f)) (λu.x) (λv.v)

    1 := succ 0
      := (λn.λf.λx. f (n f x)) (λg.λy. y)
      := λf.λx. f ((λg.λy. y) f x)
      := λf.λx. f ((λy. y) x)
      := λf.λx. f x
    2 := succ 1
      := (λn.λf.λx. f (n f x)) (λg.λy. g y)
      := λf.λx. f ((λg.λy. g y) f x)
      := λf.λx. f ((λy. f y) x)
      := λf.λx. f (f x)
    3 := succ 2
      := (λn.λf.λx. f (n f x)) (λg.λy. g (g y))
      := λf.λx. f ((λg.λy. g (g y)) f x)
      := λf.λx. f ((λy. f (f y)) x)
      := λf.λx. f (f (f x))

Arithmetic can be performed as well:

    plus := λm.λn.λf.λx. m f (n f x)
    sub := λm.λn. n (pred m)

    ⟦ M + N ⟧ := (plus M) N
    ⟦ M - N ⟧ := (sub M) N

Comparison can be achieved also:

    iszero := λn. n (λx. false) true
    leq := λm.λn. iszero (sub m n)
    eq := λm.λn. and (leq m n) (leq n m)

    ⟦ M = N ⟧ := (eq M) N

We can test tiny equations:

    ⟦ 1 + 2 ⟧ -> (plus 1) 2
              -> ((λm.λn.λf.λx. m f (n f x)) 1) 2
              -> λf.λx. 1 f (2 f x)
              -> λf.λx. (λg.λy. g y) f ((λh.λz. h (h z)) f x)
              -> λf.λx. (λy. f y) ((λh.λz. h (h z)) f x)
              -> λf.λx. (λy. f y) ((λz. f (f z)) x)
              -> λf.λx. (λy. f y) (f (f x))
              -> λf.λx. f (f (f x))
              -> 3

    (sub 2) 1 -> 1 (pred 2)
              -> 1 (λf.λx. 2 (λg.λh. h (g f)) (λu.x) (λv.v))
              -> 1 (λf.λx. (λe.λw. e (e w)) (λg.λh. h (g f)) (λu.x) (λv.v))
              -> 1 (λf.λx. (λw. (λg.λh. h (g f)) ((λd.λe. e (d f)) w)) (λu.x) (λv.v))
              -> 1 (λf.λx. ((λg.λh. h (g f)) ((λd.λe. e (d f)) λu.x)) (λv.v))
              -> 1 (λf.λx. ((λg.λh. h (g f)) (λe. e (λu.x f))) (λv.v))
              -> 1 (λf.λx. ((λg.λh. h (g f)) (λe. e x)) (λv.v))
              -> 1 (λf.λx. (λh. h ((λe. e x) f)) (λv.v))
              -> 1 (λf.λx. (λh. h (f x)) (λv.v))
              -> 1 (λf.λx. ((λv.v) (f x)))
              -> 1 (λg.λy. g y)
              -> (λf.λx. f x) (λg.λy. g y)
              -> (λx. (λg.λy. g y) x)
              -> (λx. (λy. x y))
              -> λf.λx. f x
              -> 1

    leq 2 1 -> iszero (sub 2 1)
            -> iszero 1
            -> (λn. n (λx. false) true) 1
            -> (λn. n (λx. false) true) (λg.λy. g y)
            -> (λg.λy. g y) (λx. false) true
            -> (λy. (λx. false) y) true
            -> (λy. false) true
            -> false

    (sub 1) 2 -> 2 (pred 1)
              -> 2 ((λn.λf.λx. n (λg.λh. h (g f)) (λu.x) (λv.v)) 1)
              -> 2 (λf.λx. 1 (λg.λh. h (g f)) (λu.x) (λv.v))
              -> 2 (λf.λx. (λe.λw. e w) (λg.λh. h (g f)) (λu.x) (λv.v))
              -> 2 (λf.λx. (λe.λw. e w) (λg.λh. h (g f)) (λu.x) (λv.v))
              -> 2 (λf.λx. (λw. (λg.λh. h (g f)) w) (λu.x) (λv.v))
              -> 2 (λf.λx. (λw. (λh. h (w f))) (λu.x) (λv.v))
              -> 2 (λf.λx. (λh. h ((λu.x) f)) (λv.v))
              -> 2 (λf.λx. ((λv.v) ((λu.x) f)))
              -> 2 (λf.λx. ((λv.v) x))
              -> 2 (λf.λx. x)
              -> (λf.λx. f (f x)) (λg.λy. y)
              -> λx. (λg.λy. y) ((λg.λy. y) x)
              -> λx. (λg.λy. y) (λy. y)
              -> λx.λy. y
              -> 0

    leq 1 2 -> iszero (sub 1 2)
            -> iszero 0
            -> (λn. n (λx. false) true) (λf.λy. y)
            -> (λf.λy. y) (λx. false) true
            -> (λy. y) true
            -> true

    ⟦ 2 = 1 ⟧ -> (eq 2) 1
              -> and (leq 2 1) (leq 1 2)
              -> and false true
              -> λx.λy. (false ((true x) y)) y
              -> λx.λy. ((λc.λd.d) (((λa.λb.a) x) y)) y
              -> λx.λy. ((λc.λd.d) ((λb.x) y)) y
              -> λx.λy. ((λc.λd.d) x) y
              -> λx.λy. ((λd.d) y)
              -> λx.λy. y
              -> false

The `Y` Combinator
------------------

The `Y` combinator is used for doing _recursion_ in lambda calculus:

    Y f := f (Y f)

It applies the term `Y f` - obtained by juxtaposing `f` in its _entirety_ next to `Y` - to `f` itself in its _entirety_
(i.e., not abbreviated by a definition).

The `fib`onacci recursive function in `Scala`:

```Scala
def fib(n: Long): Long =
  if n == 0 || n == 1
  then
    n
  else
    fib(n-1) + fib(n-2)
```

in lambda calculus is a closed term:

    fib := λf.λn. if (or ⟦n = 0⟧ ⟦n = 1⟧) then n else ⟦ f⟦n-1⟧ + f⟦n-2⟧ ⟧

We put in action the `Y` combinator, but for brevity and readability do _not_ juxtapose `fib` in its entirety (the right hand
side of the above abbreviation):

    (Y fib) 3 -> (fib (Y fib)) 3
              -> (λn. if (or ⟦n = 0⟧ ⟦n = 1⟧) then n else ⟦ (Y fib)⟦n-1⟧ + (Y fib)⟦n-2⟧ ⟧) 3
              -> if (or ⟦3 = 0⟧ ⟦3 = 1⟧) then 3 else ⟦ (Y fib)⟦3-1⟧ + (Y fib)⟦3-2⟧ ⟧
              -> ⟦ ((Y fib) 2) + ((Y fib) 1) ⟧
              -> ⟦ 1 + 1 ⟧
              -> 2

because:

    (Y fib) 2 -> (fib (Y fib)) 2
              -> (λn. if (or ⟦n = 0⟧ ⟦n = 1⟧) then n else ⟦ (Y fib)⟦n-1⟧ + (Y fib)⟦n-2⟧ ⟧) 2
              -> if (or ⟦2 = 0⟧ ⟦2 = 1⟧) then 2 else ⟦ (Y fib)⟦2-1⟧ + (Y fib)⟦2-2⟧ ⟧
              -> ⟦ ((Y fib) 1) + ((Y fib) 0) ⟧
              -> ⟦ 1 + 0 ⟧
              -> 1

    (Y fib) 1 -> (fib (Y fib)) 1
              -> (λn. if (or ⟦n = 0⟧ ⟦n = 1⟧) then n else ⟦ (Y fib)⟦n-1⟧ + (Y fib)⟦n-2⟧ ⟧) 1
              -> if (or ⟦1 = 0⟧ ⟦1 = 1⟧) then 1 else ⟦ (Y fib)⟦1-1⟧ + (Y fib)⟦1-2⟧ ⟧
              -> 1

    (Y fib) 0 -> (fib (Y fib)) 0
              -> (λn. if (or ⟦n = 0⟧ ⟦n = 1⟧) then n else ⟦ (Y fib)⟦n-1⟧ + (Y fib)⟦n-2⟧ ⟧) 0
              -> if (or ⟦0 = 0⟧ ⟦0 = 1⟧) then 0 else ⟦ (Y fib)⟦0-1⟧ + (Y fib)⟦0-2⟧ ⟧
              -> 0

Writing `fib` in its entirety, the usage of the `Y` combinator would appear thus:

    (λf.λn. if (or ⟦n = 0⟧ ⟦n = 1⟧) then n else ⟦ f⟦n-1⟧ + f⟦n-2⟧ ⟧) (Y (λf.λn. if (or ⟦n = 0⟧ ⟦n = 1⟧) then n else ⟦ f⟦n-1⟧ + f⟦n-2⟧ ⟧))

Let us observe that only the occurrences of the `f` variable will be replaced with `Y fib`: this carries with it the
_potential_ for recursion, because, unless a base case intervenes, it will replicate itself to `fib (Y fib)` again, in each
of those occurrences which get evaluated.

[Previous](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/recursion-2-schemes/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/recursion-4-Defer/README.md)
