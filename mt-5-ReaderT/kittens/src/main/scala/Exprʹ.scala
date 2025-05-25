import scala.util.parsing.combinator.JavaTokenParsers

object Exprʹ extends JavaTokenParsers:

  import Expr._

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
    literal

  def literal(implicit unit: unit): Parser[Expr[Int | Double]] =
    floatingPointNumber ^^ {
      _.toDouble match
        case 0d => Zero
        case 1d => One
        case n => Val(n)
    } |
    decimalNumber ^^ {
      _.toInt match
        case 0 => Zero
        case 1 => One
        case n => Val(n)
    } |
    "("~> expr <~")"

  implicit class ExprInterpolator(private val sc: StringContext) extends AnyVal:
    def x(args: Any*)(implicit unit: unit): Expr[Int | Double] =
      val inp = (sc.parts zip (args :+ "")).foldLeft("") {
        case (r, (p, a)) => r + p + a
      }
      parseAll(expr, inp).get
