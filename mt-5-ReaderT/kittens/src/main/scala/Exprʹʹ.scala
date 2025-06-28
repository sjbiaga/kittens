import cats.parse.Parser
import cats.parse.{ Parser, Parser0, Numbers }
import Parser.{ charIn, defer, end }
import Numbers.jsonNumber

object Exprʹʹ:

  import Expr.*

  private val whitespace: Parser[Unit] = charIn(" \t\r\n").void
  private val whitespaces0: Parser0[Unit] = whitespace.rep0.void

  private def char(cs: Char*): Parser[Char] = charIn(cs).surroundedBy(whitespaces0)

  def expr(implicit unit: unit): Parser[Expr[Double]] =
    (term ~ (char('+', '-') ~ term).rep0).map {
      case (lhs, rhs) => rhs.foldLeft(lhs) {
        case (lhs, ('+', rhs)) => Add(lhs, rhs)
        case (lhs, ('-', rhs)) => Sub(lhs, rhs)
      }
    }

  def term(implicit unit: unit): Parser[Expr[Double]] =
    (factor ~ (char('*', '/') ~ factor).rep0).map {
      case (lhs, rhs) => rhs.foldLeft(lhs) {
        case (lhs, ('*', rhs)) => Mul(lhs, rhs)
        case (lhs, ('/', rhs)) => Div(lhs, rhs)
      }
    }

  def factor(implicit unit: unit): Parser[Expr[Double]] =
    (char('+', '-') ~ literal).map {
      case ('-', rhs) if unit eq Zero => Inv(rhs)
      case ('+', rhs) => Add(Zero, rhs)
      case ('-', rhs) => Sub(Zero, rhs)
    } |
    literal

  def literal(implicit unit: unit): Parser[Expr[Double]] =
    jsonNumber.surroundedBy(whitespaces0).map {
      _.toDouble match
        case 0d => Zero
        case 1d => One
        case n => Val(n)
    } |
    char('(') *> defer(expr) <* char(')')

  def parserExpr(implicit unit: unit): Parser[Expr[Double]] = whitespaces0.with1 *> expr <* (whitespaces0 ~ end)

  implicit class ExprInterpolator(private val sc: StringContext) extends AnyVal:
    def x(args: Any*)(implicit unit: unit): Expr[Double] =
      val inp = (sc.parts zip (args :+ "")).foldLeft("") {
        case (r, (p, a)) => r + p + a
      }
      parserExpr.parseAll(inp).right.get
