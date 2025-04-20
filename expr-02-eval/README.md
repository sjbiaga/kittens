[First](https://github.com/sjbiaga/kittens/blob/main/expr-01-trait/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/expr-01-trait/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-03-swap/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/expr-09-ring/README.md)

Lesson 03: A Rich Language of Expressions (cont'd)
==================================================

Evaluation of Expressions
-------------------------

When mixing `Val`ues of different types (such as both `Int` and `Double`), type `T` in `Expr[T]` will be a union type (such
as `Int | Double`). For this particular case, we give a recursive evaluation algorithm:

```Scala
import Expr._
def eval(expr: Expr[Int | Double])(implicit unit: unit): Double =
  expr match
    case Zero => 0d
    case One => 1d
    case Val(n: Int) => n.toDouble
    case Val(n: Double) => n
    case Inv(n) if Zero eq unit => 0d - eval(n)
    case Inv(n) if One eq unit => 1d / eval(n)
    case Add(m, n) => eval(m) + eval(n)
    case Sub(m, n) => eval(m) - eval(n)
    case Mul(m, n) => eval(m) * eval(n)
    case Div(m, n) => eval(m) / eval(n)
```

It is important to note that the objects from which an `Expr`ession is constructed (instances of `enum` `case` classes) may
be viewed as the states of a `FSM` or the instructions of a _program_, while in this case the machine _architecture_ is _in_
the very evaluation.

The effect of the program depends on _how_ it processes those instructions. We can have, for example, a different
interpretation of `Add`itions and `Sub`tractions as maximums, respectively, minimums.

```Scala
def eval(expr: Expr[Int | Double])(implicit unit: unit): Double =
  expr match
    case Zero => 0d
    case One => 1d
    case Val(n: Int) => n.toDouble
    case Val(n: Double) => n
    case Inv(n) if Zero eq unit => 0d min eval(n)
    case Inv(n) if One eq unit => 1d / eval(n)
    case Add(m, n) => eval(m) max eval(n)
    case Sub(m, n) => eval(m) min eval(n)
    case Mul(m, n) => eval(m) * eval(n)
    case Div(m, n) => eval(m) / eval(n)
```

Although a program is the same in both cases (e.g., `Mul(Add(One, Val(-1)), One)`), the "machine" (architecture) differs, with
the results of evaluation equal to, respectively, `0d` and `1d`.

[First](https://github.com/sjbiaga/kittens/blob/main/expr-01-trait/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/expr-01-trait/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-03-swap/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/expr-09-ring/README.md)
