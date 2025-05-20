package ʹʹʹ

import ExprF._

object Main:

  def main(args: Array[String]): Unit =
    val e1 = Mul(IfNeg(Mul(One, Var("a")), Add(Var("b"), Zero), Add(Var("b"), Val(2L))), Val(3L))
  
    println {
      vars(e1)
    }

    {
      given Map[String, Expr] = Map(
        "b" -> Var("a")
      )
    
      println {
        subst(e1)
      }
    }

    {
      given Map[String, Long] = Map(
        "a" -> 5,
        "b" -> 7
      )
    
      println {
        eval(e1)
      }
    }
