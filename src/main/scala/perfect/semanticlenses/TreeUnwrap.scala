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
// The new output is included in the original tree.
object TreeUnwrap extends CustomProgramFormula  {
  object Eval {
    def unapply(e: Expr)(implicit symbols: Symbols): Option[Expr] = e match {
      case Goal(tpe, a, argsInSequence) =>
        argsInSequence match {
          case Nil => Some(a)
          case head :: tail =>
            a match {
              case ADT(ADTType(adtid, tps), args) =>
                symbols.adts(adtid) match {
                  case f: ADTConstructor =>
                    val i = f.selectorID2Index(head)
                    unapply(Goal(tpe, args(i), tail))
                  case _ => None
                }
              case _ => None
            }
        }
      case _ => None
    }
  }
  def merge(e1: Expr, e2: Expr)(implicit symbols: Symbols): Option[(Expr, Seq[(Variable, KnownValue)])] = {
    e1 match { case Goal(tpeGlobal, unwrap, l) =>
      e2 match { case Goal(tpeGlobal2, unwrap2, l2) =>
        Log(s"[internal warning]: Merge of two Tree unwrap not supported $e1, $e2")
        None
      case _ => None
      }
    case _ => None
    }
  }



  object Lens extends SemanticLens {
    def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
      out.simplifiedExpr match {
      case TreeUnwrap.Goal(tpe, original, l) =>
        l match {
        case Nil => Stream(in.assignmentsAsOriginals())
        case head :: tail =>
          in.expr match {
          case l@ADT(ADTType(adtid, tps), args) =>
            symbols.adts(adtid) match {
            case f: ADTConstructor =>
              val i = f.selectorID2Index(head)
              return repair(in.subExpr(args(i)), TreeUnwrap(tpe, args(i), tail) combineWith out.formula)
            case _ => Stream.empty
            }
          case _ => Stream.empty
          }
        }
      case _ => Stream.empty
      }
    }
    isPreemptive = true
  }

  def apply(tpe: Type, original: Expr, argsInSequence: List[Identifier]): ProgramFormula = {
    ProgramFormula(Goal(tpe, original, argsInSequence))
  }
  def unapply(pf: ProgramFormula): Option[(Type, Expr, List[Identifier])] = {
    Goal.unapply(pf.expr)
  }
  val Goal = lenses.TreeUnwrapGoal
}

