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
/** A sub-element of the tree has been modified. */
object TreeModification extends CustomProgramFormula {
  object Eval {
    def unapply(e: Expr)(implicit symbols: Symbols): Option[Expr] = e match {
      case Goal(tpeGlobal, tpeLocal, original, modified, argsList) =>
        Some(Goal.LambdaPath(original, argsList, modified).getOrElse(e))
      case _ => None
    }
  }

  def merge(e1: Expr, e2: Expr)(implicit symbols: Symbols): Option[(Expr, Seq[(Variable, KnownValue)])] = {
    e1 match { case Goal(tpeGlobal, tpeLocal, before, _, _) =>
      e2 match { case Goal(tpeGlobal2, tpeLocal2, before2, _, _) =>
        Log(s"[internal warning]: Merge of two Tree modification not supported $e1, $e2")
        None
      case _ => None
      }
    case _ => None
    }
  }


  object Lens extends SemanticLens {
    def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
      out.simplifiedExpr match {
        case TreeModification.Goal(tpeG, tpeL, original, modified, l) =>
          l match {
            case Nil =>
              repair(in, out.subExpr(modified))
            case head :: tail =>
              in.expr match {
                case l@ADT(ADTType(adtid, tps), args) =>
                  symbols.adts(adtid) match {
                    case f: ADTConstructor =>
                      val i = f.selectorID2Index(head)
                      original match {
                        case ADT(_, argsOriginal) =>
                          val subOriginal = argsOriginal(i)
                          for {pf <- repair(in.subExpr(args(i)),
                            TreeModification(subOriginal.getType, tpeL, subOriginal, modified, tail) combineWith out.formula)} yield {
                            pf.wrap(x =>
                              ADT(l.adt, args.take(i) ++ List(x) ++ args.drop(i + 1)))
                          }
                      }
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

  def apply(tpeGlobal: Type, tpeLocal: Type, original: Expr, modified: Expr, argsInSequence: List[Identifier])(implicit symbols: Symbols): ProgramFormula = {
    ProgramFormula(Goal(tpeGlobal, tpeLocal, original, modified, argsInSequence))
  }
  def unapply(pf: ProgramFormula)(implicit symbols: Symbols): Option[(Type, Type, Expr, Expr, List[Identifier])] =
    Goal.unapply(pf.expr)

  val Goal = TreeModificationGoal
}
