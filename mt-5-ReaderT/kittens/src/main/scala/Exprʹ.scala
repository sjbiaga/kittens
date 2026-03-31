import scala.util.parsing.combinator.JavaTokenParsers

object Exprʹ extends JavaTokenParsers:

  import Expr.*

  def expr(using unit): Parser[Expr[Double]] =
    term ~ rep(("+"|"-") ~ term) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "+" ~ rhs) => Add(lhs, rhs)
        case (lhs, "-" ~ rhs) => Sub(lhs, rhs)
      }
    }

  def term(using unit): Parser[Expr[Double]] =
    factor ~ rep(("*"|"/") ~ factor) ^^ {
      case lhs ~ rhs => rhs.foldLeft(lhs) {
        case (lhs, "*" ~ rhs) => Mul(lhs, rhs)
        case (lhs, "/" ~ rhs) => Div(lhs, rhs)
      }
    }

  def factor(using unit): Parser[Expr[Double]] =
    ("+"|"-") ~ literal ^^ {
      case "-" ~ rhs if summon[unit] eq Zero => Inv(rhs)
      case "+" ~ rhs => Add(Zero, rhs)
      case "-" ~ rhs => Sub(Zero, rhs)
    } |
    literal

  def literal(using unit): Parser[Expr[Double]] =
    floatingPointNumber ^^ {
      _.toDouble match
        case 0d => Zero
        case 1d => One
        case n => Val(n)
    } |
    "("~> expr <~")"

  implicit class ExprInterpolator(private val sc: StringContext) extends AnyVal:
    def x(args: Any*)(using unit): Expr[Double] =
      val inp = (sc.parts zip (args :+ "")).foldLeft("") {
        case (r, (p, a)) => r + p + a
      }
      parseAll(expr, inp).get
