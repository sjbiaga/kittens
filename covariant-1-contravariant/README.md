[Next](https://github.com/sjbiaga/kittens/blob/main/covariant-2-contravariant/README.md)

Lesson 01: Covariant vs Contravariant Types
===========================================

A [higher-kinded type](https://scalawithcats.com/dist/scala-with-cats-1.html#aside-higher-kinds-and-type-constructors),
or type constructor, `T[+A]` is _covariant_ in the type parameter `A`, if this is prefixed by "`+`".

Type `S[-B]` is _contravariant_ in the type parameter `B`, if this is prefixed by "`-`". `S` and `T` have kind `* -> *`.

However, if the type parameter is a type constructor `V[_]`, then `U[V[_]]` has kind `(* -> *) -> *`. We can request that `U`
be contravariant (in `V`) with `U[-V[_]]`, or that `V` be covariant with `U[V[+_]]`.

All three `S`, `T` and `U` are generic, but they differ in their kind. `A` and `B` have kind `*`, meaning they are _not_
higher-kinded.

Let us look at `Function1[-A, +B]` trait, for example. It has one abstract `apply` method:

```Scala
def apply(arg: A): B
```

We can see that a _function_ is contravariant in the type of its parameter, and covariant in the type of its result (or
_return type_). We shall use this simple observation when we discuss variance.

Subtype relation
----------------

Variance would remain a formal game, were it not for inheritance, which induces a _subtype_ relation between types (traits,
classes).

Let us introduce as a running example, a class hierarchy of animals:

```Scala
class Animal
class Pet extends Animal
```

Indeed, we can verify that `Pet` is a subtype of `Animal`, with a witness or _evidence_ of this fact:

```Scala
implicitly[Pet <:< Animal]
```

On the contrary, there is no `implicit` (evidence) of the otherwise:

```scala
scala> implicitly[Animal <:< Pet]
-- [E172] Type Error: ----------------------------------------------------------
1 |implicitly[Animal <:< Pet]
  |                          ^
  |                          Cannot prove that Animal <:< Pet.
1 error found
```

The induced relation is that `Pet` is a subtype of `Animal`. Essentially, this may be observed in assignments, going from
`Pet` to `Animal`, or the other way around:

```Scala
val p: Pet = new Animal // (1) does not compile
val p: Animal = new Pet // (2) compiles OK
```

Because `Pet` is a subtype of `Animal`, we may invoke methods on `Pet` that belong to class `Animal`, but not vice-versa,
meaning we can use an object of type `Pet` as an object of type `Animal`, or by assigning an object of the subtype to a value
of the supertype. So (2) above compiles, whereas (1) does not: an object of the top type `Animal` class can be "any animal",
not "just a pet".

So, in general, given two types `D` and `C` in the subtype relation, all of the following three lines compile:

```Scala
implicitly[D <:< C]
val subtype: D = ???
val supertype: C = subtype
```

Variance comes into play when _generics_ are involved. Let us introduce two more classes derived from `Pet`:

```Scala
class Cat extends Pet
class Dog extends Pet
```

Contravariance
--------------

Let us further picture a contravariant class `A[-P <: Pet]` - or, equivalently, a class with a method with one parameter of
type that of the parameter type `P <: Pet` (notice how this has an _upper_ bound):

```Scala
class A[-P <: Pet] { def m(p: P): Unit = println(p.getClass) }
val a = new A[Pet]
```

Our intuition tells us that we can invoke method `a.m` with the parameter `p` the instances of `Cat` or `Dog` (or "pets").

Now, contravariance for generics dictates that because `Cat` is a subtype of `Pet`, and type constructor `A` is contravariant
in the type parameter `P`, then `A[Pet]` be a subtype of `A[Cat]`, so that we can apply the "three lines rule" and assign `a`
to a value of type `A[Cat]`:

```Scala
val c: A[Cat] = a
```

[Note that `A` is _not a collection_, where from we might have supposedly obtained elements of type `P` in the return types
of some other method(s).]

We can, henceforth, invoke the method `c.m` with argument the instances of `Cat`. Of course, we could have invoked method
`a.m` with argument instances of `Dog`. So, the question is: we did before pass `Dog`s to method `m`, and after we restrict
to the use of `Cat`s? But note again that we did _not_ "add/remove" dogs to/from a purported "collection"! The implementation
of `m` prints the (name of the) `Class` of a pet, and forgets all about this parameter.

So, the answer is that, after the assignment to `c`, from then on, value `a` may _only_ be used as a generic of type `A[Cat]`.

An actual use of a contravariant parameter is in the case of `Function1[-S, +T]`. Suppose we had a function to count the legs
of dogs: this would be the constant `4` function.

```Scala
val legs4dogs: Dog => Int = { _ => 4 } // (1)
val legs4pets: Pet => Int = legs4dogs  // (2) does not compile
```

Intuition tells us again that we could not count the legs of pets using a function that counts the legs of dogs! Indeed, as
`Dog` is a subtype of `Pet`, and `Function1` is contravariant in its arguments' type parameter, `Pet => Int` is a subtype of
`Dog => Int`, and not the other way around: hence, by the "three lines rule", (2) above does not compile.

On the contrary, had we had a function to count the legs of `Pet`s:

```Scala
val legs4pets: Pet => Int = { case _: Cat | _: Dog => 4 } // (1)
val legs4dogs: Dog => Int = legs4pets                     // (2)
```

then `Dog` a subtype of `Pet` implies the assignment (2) above does compile; and is intuitively correct: counting the legs of
pets includes as a subcase counting the legs of `Dog`s.

Covariance
----------

Collections are a classical example of covariance: `List`, `Map` (in its second type parameter, for values), `Option`,
`Either` are all covariant types.

Thus, let us picture a covariant class `B[+P >: Pet]` - or, equivalently, a class with a method with the return type that of
the parameter type `P >: Pet` (notice how this has a _lower_ bound):

```Scala
class B[+P >: Pet] { def m: P = new Cat }
val b = new B[Pet]
```

Method `b.m` is parameterless and returns objects whose types have `Pet` as lower bound: these are `Animal` and `Pet`. Out of
the question to assign `b` to a value of type `B[Cat]` or `B[Dog]`.

But because `Pet` is a subtype of `Animal`, by the "three lines  rule", we can assign `b` to a value of type `B[Animal]`:

```Scala
val a: B[Animal] = b
println(a.m.getClass)
```

This is in conformance with our intuition: as `b.m` returns a `Cat`, `a.m` may return an `Animal`; that is, wherever we
require an `Animal`, we can pass a `Cat`.

A notable use case is of the bottom type `Nothing` in `case object`s, such as `Nil: List[Nothing]` or `None: Option[Nothing]`:
because these are covariant, and as `Nothing` is a subtype of `Int` and of `String`, the next two lines compile:

```Scala
var ls: List[Int] = Nil
var opt: Option[String] = None
```

`List[Nothing]` being a subtype of `List[Int]`, and `Option[Nothing]` being a subtype of `Option[String]`.

Another interesting thing - related to collections - with respect to covariance, is what happens with methods that take as
parameter objects of the element type, such as `contains` or `updated` (the latter, only in the case of `List`):

```Scala
def contains[A1 >: A](elem: A1): Boolean
def updated[B >: A](index: Int, elem: B): List[B]
```

We can see that the solution here is to impose a _lower bound_ to the parameter type. Otherwise, using the original type
parameter `A`:

```Scala
def contains(elem: A): Boolean            // compile error
def updated(index: Int, elem: A): List[A] // compile error
```

would generate a compile error, as the covariant type parameter `A` would occurr in contravariant positions. The occurrence
of `A` in `A1 >: A` or `B >: A`, is also in a covariant position.

[Next](https://github.com/sjbiaga/kittens/blob/main/covariant-2-contravariant/README.md)
