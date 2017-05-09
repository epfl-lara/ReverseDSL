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
      out.simplifiedExpr match {
        case StringConcat(outArg1, outArg2) =>
          in.expr match {
            case StringConcat(expr1, expr2) =>
              ProgramFormula.repairArguments(in.formula, Seq((expr1, out.subExpr(outArg1)), (expr2, out.subExpr(outArg2)))).map{ case (args, f) =>
                ProgramFormula(StringConcat(args(0), args(1)), f)
              }
            case _ => Stream.empty
          }
        case _ =>
          in.expr match {
            case StringLiteral(_) =>
              out.expr match {
                case StringInsert.Expr(left, inserted, right, direction) =>
                  Stream(ProgramFormula(StringLiteral(left + inserted + right)))
                case _ => Stream(out)
              }
            case StringConcat(expr1, expr2) =>
              val expr1val = in.formula.assignments.flatMap(assign => maybeEvalWithCache(assign(expr1)))
              val expr2val = in.formula.assignments.flatMap(assign => maybeEvalWithCache(assign(expr2)))
              Utils.ifEmpty {
                if (expr1val.isEmpty || expr2val.isEmpty) {
                  Stream.empty
                } else {
                  val expr1v = expr1val.get
                  val expr2v = expr2val.get
                  ReverseProgram.StringConcatLens.put(Nil)(Seq(in.subExpr(expr1v), in.subExpr(expr2v)), out).flatMap { case (args, f) =>
                    ProgramFormula.repairArguments(in.formula, Seq((expr1, args(0)), (expr2, args(1)))).map{ case (args2, f2) =>
                      ProgramFormula(StringConcat(args2(0), args2(1)), f combineWith f2 combineWith args(0).formula combineWith args(1).formula)
                    }
                  }
                }
              } {
                // We want to avoid at maximum having to solve constraints.
                Stream(ProgramFormula(in.expr, Formula(Map(), out.expr === in.expr)))
              } #::: {
                out.expr match {
                  // Handles insertion between two non-constants as a possible constant at the last resort.
                  case StringInsert.Expr(left, inserted, right, direction) if !expr1.isInstanceOf[StringLiteral] && !expr2.isInstanceOf[StringLiteral] &&
                    expr1val == Some(StringLiteral(left)) &&
                    expr2val == Some(StringLiteral(right)) =>
                    Stream(in.subExpr(expr1 +& StringLiteral(inserted) +& expr2).assignmentsAsOriginals())
                  case _ => Stream.empty
                }
              }
            case _ => Stream.empty
          }
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

