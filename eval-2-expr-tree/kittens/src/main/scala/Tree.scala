import cats.Monad

enum Op:
  case Add, Sub, Mul, Div, Inv

enum Tree[+T]:
  val result: T
  case Leaf[+T](override val result: T) extends Tree[T]
  case Node[+T](override val result: T,
                operator: Op,
                left: Option[Tree[T]],
                right: Option[Tree[T]]) extends Tree[T]

object Tree:
  implicit val kittensTreeMonad: Monad[Tree] =
    new Monad[Tree]:
      def pure[A](a: A): Tree[A] = Leaf(a)
      override def flatten[A](fa: Tree[Tree[A]]): Tree[A] =
        fa.result
      override def map[A, B](fa: Tree[A])(f: A => B): Tree[B] =
        fa match
          case Leaf(a)                           => Leaf(f(a))
          case Node(a, Op.Inv, _,       Some(n)) => Node(f(a), Op.Inv, None,            Some(map(n)(f)))
          case Node(a, Op.Add, Some(m), Some(n)) => Node(f(a), Op.Add, Some(map(m)(f)), Some(map(n)(f)))
          case Node(a, Op.Sub, Some(m), Some(n)) => Node(f(a), Op.Sub, Some(map(m)(f)), Some(map(n)(f)))
          case Node(a, Op.Mul, Some(m), Some(n)) => Node(f(a), Op.Mul, Some(map(m)(f)), Some(map(n)(f)))
          case Node(a, Op.Div, Some(m), Some(n)) => Node(f(a), Op.Div, Some(map(m)(f)), Some(map(n)(f)))
      def flatMap[A, B](fa: Tree[A])(f: A => Tree[B]): Tree[B] =
        flatten(map(fa)(f))
      final def tailRecM[A, B](a: A)(f: A => Tree[Either[A, B]]): Tree[B] =
        flatMap(f(a))(_.fold(tailRecM(_)(f), pure))
