[First](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/nat-3-trampoline/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-simplify/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/nat-4-list/README.md)

Lesson 06: Natural Transformations (cont'd)
===========================================

We recall the definition of `Trampoline`:

```Scala
import cats.~>

sealed abstract trait Trampoline[A]:
  import Trampoline.*

  def visit[F[_]](v: Visitor[F]): F[A]

  final def map[B](fun: A => B): Trampoline[B] =
    this.flatMap(fun andThen pure)

  final def flatMap[B](sequel: A => Trampoline[B]): Trampoline[B] =
    FlatMap(this, sequel)

  final def apply(): A = this match
    case Done(value) => value
    case Call(closure) => closure(())()
    case FlatMap(Done(value), sequel) => sequel(value)()
    case FlatMap(Call(closure), sequel) => (closure :: sequel)(())()
    case FlatMap(FlatMap(self, prequel), sequel) => FlatMap(self, prequel :: sequel)()

object Trampoline:

  trait Visitor[F[_]] extends (Trampoline ~> F):
    final override def apply[A](ta: Trampoline[A]): F[A] = ta.visit(this)

    def done[A](value: A): F[A]
    final def call[A](closure: Unit => Trampoline[A]): F[A] = fMap(Done(()), closure)
    def fMap[A, B](self: Trampoline[A], cont: A => Trampoline[B]): F[B]

  extension [A, B](prequel: A => Trampoline[B])
    inline def ::[C](sequel: B => Trampoline[C]): A => Trampoline[C] =
      prequel(_).flatMap(sequel)

  final case class Done[A](value: A) extends Trampoline[A]:
    override def visit[F[_]](v: Visitor[F]): F[A] = v.done(value)

  final case class Call[A](closure: Unit => Trampoline[A]) extends Trampoline[A]:
    override def visit[F[_]](v: Visitor[F]): F[A] = v.call(closure)

  final case class FlatMap[A, B](self: Trampoline[A], sequel: A => Trampoline[B]) extends Trampoline[B]:
    override def visit[F[_]](v: Visitor[F]): F[B] = v.fMap(self, sequel)

  def pure[A](a: A): Trampoline[A] = new Done(a)

  object Call:
    def apply[A](thunk: => Trampoline[A]): Trampoline[A] = Call { _ => thunk }

implicit val kittensTrampolineDeferInstance: Defer[Trampoline] =
  new Defer[Trampoline]:
    override def defer[A](fa: => Trampoline[A]): Trampoline[A] = Trampoline.Call(fa)
```

and that of a `MonadInterpreter` which wraps the nested singleton object that implements `Trampoline.Visitor[M]`:

```Scala
import cats.{ Defer, Monad }
import cats.syntax.all.*

class MonadInterpreter[M[_]: Monad: Defer]:
  val M = Monad[M]
  val D = Defer[M]
  object TrampolineInterpreter extends Trampoline.Visitor[M]:
    def done[A](value: A): M[A] = M.pure(value)
    def fMap[A, B](self: Trampoline[A], cont: A => Trampoline[B]): M[B] =
      M.flatMap(D.defer(apply(self)))(cont andThen apply)
```

We will require also the following imports:

```Scala
import cats.*, cats.free.{ Trampoline => CatsTrampoline, * }, cats.instances.tailRec.*
import scala.util.control.TailCalls.TailRec
import cats.effect.unsafe.implicits.global, cats.effect.IO
```

The N Queens Problem - the "trampoline" algorithm: with Natural Transformations
-------------------------------------------------------------------------------

We will use the same implementation as in
[Lesson 04 - The N Queens Problem - the "trampoline" algorithm](https://github.com/sjbiaga/kittens/blob/main/queens-3-trampoline/README.md#the-n-queens-problem---the-trampoline-algorithm):

```Scala
def queens[M[_]: Monad](using M: Long, board: Board): M[Unit] =
  var maxSolutions = M
  def tqueens(k: Int, q: Point)(implicit currentSolution: Solution): Trampoline[Unit] =
    if q.row == board.N
    then
      Done(())
    else if k == 0
    then
      if currentSolution.length == board.N && Validator(currentSolution)
      then
        println(currentSolution.sorted)
        maxSolutions -= 1
        if maxSolutions == 0
        then
          throw MaxSolutionsReached
      Done(())
    else if q.col == board.N
    then
      Call { tqueens(k, q.row + 1 x 0) }
    else
      for
        _ <- Call { tqueens(k, q.row x q.col + 1) }
        _ <- Call {
          if !board(q.row)(q.col)
          then
            tqueens(k - 1, q.row x q.col + 1)(q :: currentSolution)
          else
            Done(())
        }
      yield
        ()
  val I = MonadInterpreter[M].TrampolineInterpreter
  I.apply(kittensTrampolineDeferInstance.defer(tqueens(board.N, 0 x 0)(Nil)))
```

with the exception that the outer `queens` method instantiates an interpreter:

```Scala
val I = MonadInterpreter[M].TrampolineInterpreter
```

and applies it to the very first return - to be _compiled_, now just _deferred_ - value of `tqueens`:

```Scala
I.apply(kittensTrampolineDeferInstance.defer(tqueens(board.N, 0 x 0)(Nil)))
```

Thereafter, we can invoke `queens` with whatever monad instance we have in scope:

```Scala
given Board = new EmptyBoard(4)
given Long = 2 // max number of solutions

def qEval = try queens[Eval].value catch MaxSolutionsReached => ()
def qTailRec = try queens[TailRec].result catch MaxSolutionsReached => ()
def qIO = try queens[IO].unsafeRunSync() catch MaxSolutionsReached => ()
def qCatsTrampoline = try { val f = queens[CatsTrampoline].runTailRec; f() } catch MaxSolutionsReached => ()
//def qId = try queens[Id] catch MaxSolutionsReached => ()
```

which will translate from `Trampoline` low-level language to monad's high-level tiny - `pure` and `flatMap` - language; as
well as - via the typeclass instance of the `Monad` typeclass for `Trampoline`:

```Scala
import cats.StackSafeMonad

implicit val kittensTrampolineMonadInstance: Monad[Trampoline] =
  new StackSafeMonad[Trampoline]:
    //override def ap[A, B](ff: Trampoline[A => B])(fa: Trampoline[A]): Trampoline[B] =
    //  flatMap(ff)(map(fa)(_))
    //override def flatten[A](ffa: Trampoline[Trampoline[A]]): Trampoline[A] =
    //  flatMap(ffa)(identity)
    override def flatMap[A, B](fa: Trampoline[A])(fun: A => Trampoline[B]): Trampoline[B] =
      fa.flatMap(fun)
    //override def map[A, B](fa: Trampoline[A])(fun: A => B): Trampoline[B] =
    //  fa.map(fun)
    override def pure[A](a: A): Trampoline[A] = Trampoline.pure(a)
```

we can translate from `Trampoline` to itself:

```Scala
def qTrampoline = try queens[Trampoline]() catch MaxSolutionsReached => ()
```

Now, we can see that all invocations of `queens` return the same value:

```Scala
qEval
qTailRec
qIO
qCatsTrampoline
qTrampoline
//qId
```

The last - `qId` -, however, is _not stack safe_, and, hence, it does not have a `Defer[Id]` typeclass instance.

[First](https://github.com/sjbiaga/kittens/blob/main/nat-2-trampoline/README.md) [Previous](https://github.com/sjbiaga/kittens/blob/main/nat-3-trampoline/README.md) [Next](https://github.com/sjbiaga/kittens/blob/main/expr-simplify/README.md) [Last](https://github.com/sjbiaga/kittens/blob/main/nat-4-list/README.md)
