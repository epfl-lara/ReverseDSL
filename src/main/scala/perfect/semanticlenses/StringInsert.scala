package perfect
package semanticlenses

import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.ProgramFormula.CustomProgramFormula
import perfect.ReverseProgram.{Cache, maybeEvalWithCache, repair}
import perfect.StringConcatExtended._

/**
  * Created by Mikael on 05/05/2017.
  */
/** To build and extract a StringInsert specification. Works for modifications as well */
object StringInsert extends Enumeration with CustomProgramFormula  {
  object Eval {
    def unapply(e: Expr)(implicit symbols: Symbols): Option[Expr] = e match {
      case Expr(left, middle, right, direction) => Some(StringLiteral(left + middle + right))
      case _ => None
    }
  }

  def merge(e1: Expr, e2: Expr)(implicit symbols: Symbols): Option[(Expr, Seq[(Variable, KnownValue)])] = {
    e1 match { case Expr(left, insert, right, direction) =>
      e2 match { case Expr(left1, insert1, right1, direction1) =>
        Log(s"[internal warning]: Merge of two String insert not supported $e1, $e2")
        None
      case _ => None
      }
    case _ => None
    }
  }



  object Lens extends SemanticLens {
    def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
      out match {
        case StringInsert(left, inserted, right, direction) =>
          in.expr match {
            // Values (including lambdas) should be immediately replaced by the new value
            case l: Literal[_] =>
              Stream(ProgramFormula(StringLiteral(left + inserted + right)))
            case _ => Stream.empty
          }
        case _ => Stream.empty
      }
    }
  }

  private val InsertString = FreshIdentifier("insertString")

  import AssociativeInsert._

  def computeDirection(left: String, s: String, right: String): InsertDirection = {
    val leftJump = ReverseProgram.StringConcatLens.typeJump(left, s)
    val rightJump = ReverseProgram.StringConcatLens.typeJump(s, right)
    if(leftJump < rightJump) {
      InsertToLeft
    } else if(leftJump > rightJump) {
      InsertToRight
    } else {
      InsertAutomatic
    }
  }

  /** Need a preference to attach to left or right. If not specified, will try to infer it from the expressions
    * @param left The untouched string to the left of the insertion (may have removals)
    * @param s The newly inserted string
    * @param right The untouched string to the right of the insertion (may have removals)
    * @param direction -1 if the insertion should be inserted to left, 1 to right, 0 if automatically guessed.
    **/
  def apply(left: String, s: String, right: String, direction: InsertDirection): ProgramFormula = {
    ProgramFormula(Expr(left, s, right, direction))
  }

  def unapply(f: ProgramFormula): Option[(String, String, String, InsertDirection)] = {
    Expr.unapply(f.expr)
  }

  object Expr {
    def apply(left: String, s: String, right: String, direction: InsertDirection): Expr = {
      E(InsertString)(StringLiteral(left), StringLiteral(s), StringLiteral(right), StringLiteral(direction.toString))
    }

    def unapply(e: Expr): Option[(String, String, String, InsertDirection)] = {
      e match {
        case FunctionInvocation(InsertString, Seq(), Seq(
        StringLiteral(leftBefore), StringLiteral(inserted), StringLiteral(rightBefore), StringLiteral(AssociativeInsert(direction))
        )) =>
          Some((leftBefore, inserted, rightBefore, direction))
        case _ =>
          None
      }
    }
  }

  def funDef = mkFunDef(InsertString)(){ case _ =>
    (Seq("left"::StringType, "inserted"::StringType, "right"::StringType, "direction"::StringType),
      StringType,
      {
        case Seq(left, inserted, right, direction) =>
          left +& inserted +& right // Dummy
      })
  }
}

