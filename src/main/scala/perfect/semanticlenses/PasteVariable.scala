package perfect
package semanticlenses

import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.ProgramFormula.CustomProgramFormula
import perfect.ReverseProgram.{Cache, maybeEvalWithCache, repair}
import perfect.StringConcatExtended._
import perfect.core.predef.AssociativeInsert


/**
  * Created by Mikael on 05/05/2017.
  */
/** Paste a previously cloned variable. Like  StringInsert but with a variable inside it. */
object PasteVariable extends Enumeration with CustomProgramFormula  {
  object Eval {
    def unapply(arg: Expr)(implicit symbols: Symbols): Option[Expr] = arg match {
      case Goal(left, insertedVar, originalVarValue, right, direction) =>
        Some(StringLiteral(left + originalVarValue + right))
      case _ => None
    }
  }
  def merge(e1: Expr, e2: Expr)(implicit symbols: Symbols): Option[(Expr, Seq[(Variable, KnownValue)])] = {
    e1 match { case PasteVariable.Goal(left, v, v_value, right, direction) =>
      e2 match { case PasteVariable.Goal(left2, v2, v2_value, right2, direction2) =>
        Log(s"[internal warning]: Merge of two paste exprs not supported $e1, $e2")
        None
      case _ => None
      }
    case _ => None
    }
  }

  object Lens extends SemanticLens {
    def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
      out.simplifiedExpr match {
        case PasteVariable.Goal(left, v2, v2_value, right, direction) =>
          in.expr match {
            case l: Literal[_] =>
              val newExpr = StringLiteral(left) +<>& v2 +<>& StringLiteral(right)
              Stream(ProgramFormula(newExpr, out.formula))
            case v@Variable(id, tpe, flags) =>
              in.getFunctionValue match {
                case Some(StringLiteral(s)) =>
                  def insertLeft = (if(left == s) {
                    if(right != "") {
                      Stream(ProgramFormula(v +& v2 +& StringLiteral(right)))
                    } else {
                      Stream(ProgramFormula(v +& v2))
                    }
                  } else Stream.empty) /:: Log.insertLeft
                  def insertRight = (if(right == s) {
                    if(left != "") {
                      Stream(ProgramFormula(StringLiteral(left) +& v2 +& v))
                    } else {
                      Stream(ProgramFormula(v +& v2))
                    }
                  } else Stream.empty) /:: Log.insertRight

                  def propagate = (if(left != s && right != s &&
                    s.startsWith(left) && s.endsWith(right) &&
                    s.length >= left.length + right.length ) {
                    // We need to propagate this paste to higher levels.
                    Stream(ProgramFormula(v, out.formula combineWith (v -> StrongValue(out.expr))))
                  } else Stream.empty) /:: Log.propagate
                  insertLeft #::: insertRight #::: propagate

                case _ => Stream.empty
              }


            case _ => Stream.empty
          }
        case _ => Stream.empty
      }
    }
    isPreemptive = true
  }

  def apply(left: String, insertedVar: Variable, originalVarValue: String, right: String, direction: AssociativeInsert.InsertDirection): ProgramFormula = {
    ProgramFormula(Goal(left, insertedVar, originalVarValue, right, direction))
  }

  def unapply(f: ProgramFormula): Option[(String, Variable, String, String, AssociativeInsert.InsertDirection)] = {
    Goal.unapply(f.expr)
  }

  val Goal = PasteVariableGoal
}

