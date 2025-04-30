Lessons of Scala Cats
=====================

[Lesson 01: Covariant vs Contravariant Types](https://github.com/sjbiaga/kittens/blob/main/covariant-1-contravariant/README.md)

  - [Exercise 01.1](https://github.com/sjbiaga/kittens/blob/main/covariant-2-contravariant/README.md#exercise-011)

[Lesson 02: Closures and Stack Safety](https://github.com/sjbiaga/kittens/blob/main/queens-1-native/README.md)

[Lesson 03: A Rich Language of Expressions](https://github.com/sjbiaga/kittens/blob/main/expr-01-trait/README.md)

  - [Exercise 03.1](https://github.com/sjbiaga/kittens/blob/main/expr-CoflatMap/README.md#exercise-031)

  - [Exercise 03.2](https://github.com/sjbiaga/kittens/blob/main/expr-09-ring/README.md#exercise-032)

[Lesson 04: Trampoline and Monads](https://github.com/sjbiaga/kittens/blob/main/queens-3-trampoline/README.md)

  - [Exercise 04.1](https://github.com/sjbiaga/kittens/blob/main/kleisli-2-trampoline/README.md#exercise-041)

[Lesson 05: Monoids](https://github.com/sjbiaga/kittens/blob/main/monoid-1-option/README.md)

[Lesson 06: Natural Transformations](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md)

  - [Exercise 06.1](https://github.com/sjbiaga/kittens/blob/main/expr-simplify/README.md#exercise-061)

  - [Exercise 06.2](https://github.com/sjbiaga/kittens/blob/main/expr-paired/README.md#exercise-062)

  - [Exercise 06.3](https://github.com/sjbiaga/kittens/blob/main/expr-tree/README.md#exercise-063)

  - [Exercise 06.4](https://github.com/sjbiaga/kittens/blob/main/expr-eert/README.md#exercise-064)

  - [Exercise 06.5](https://github.com/sjbiaga/kittens/blob/main/eval-1-function0/README.md#exercise-065)

  - [Exercise 06.6](https://github.com/sjbiaga/kittens/blob/main/eval-2-expr-tree/README.md#exercise-066)

  - [Exercise 06.7](https://github.com/sjbiaga/kittens/blob/main/nat-4-list/README.md#exercise-067)

[Lesson 07: Traversable](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md)

  - [Exercise 07.1](https://github.com/sjbiaga/kittens/blob/main/traverse-1-list/README.md#exercise-071)

  - [Exercise 07.2](https://github.com/sjbiaga/kittens/blob/main/traverse-3-lazylist/README.md#exercise-072)

  - [Exercise 07.3](https://github.com/sjbiaga/kittens/blob/main/traverse-3-lazylist/README.md#exercise-073)

  - [Exercise 07.4](https://github.com/sjbiaga/kittens/blob/main/traverse-5-set-expr/README.md#exercise-074)

  - [Exercise 07.5](https://github.com/sjbiaga/kittens/blob/main/traverse-6-list/README.md#exercise-075)

  - [Exercise 07.6](https://github.com/sjbiaga/kittens/blob/main/traverse-7-poke/README.md#exercise-076)

[Lesson 08: Monad Transformers](https://github.com/sjbiaga/kittens/blob/main/mt-1-compose/README.md)

  - [Exercise 08.1](https://github.com/sjbiaga/kittens/blob/main/mt-6-WriterT/README.md#exercise-081)

  - [Exercise 08.2](https://github.com/sjbiaga/kittens/blob/main/mt-8-ExprT/README.md#exercise-082)

  - [Exercise 08.3](https://github.com/sjbiaga/kittens/blob/main/mt-7-StateT/README.md#exercise-083)

  - [Exercise 08.4](https://github.com/sjbiaga/kittens/blob/main/mt-7-StateT/README.md#exercise-084)

  - [Exercise 08.5](https://github.com/sjbiaga/kittens/blob/main/mt-9-WriterT-Validated/README.md#exercise-085)

Examples
========

Make a backup of `~/.dotty_history`, then copy the `.dotty_history` from some lesson, and launch the `REPL`:

    scala-cli repl -S 3.7.0-RC4 --dep org.typelevel::cats-effect:3.7-4972921 \
                                --dep org.typelevel::cats-core:2.13.0 \
                                --dep org.typelevel::cats-free:2.13.0 \
                                --dep org.typelevel::algebra:2.13.0 \
                                --dep org.scala-lang.modules::scala-parser-combinators:2.4.0

Execute _each_ line from the beginning, in that order.

Projects
========

Each project is named `kittens` built with `SBT` developed in Scala 3.
