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
      case Goal.All(Lambda(Seq(x), body), modified, path) =>
        Some(exprOps.replaceFromSymbols(Map(x.toVariable -> modified), body))
      case _ => None
    }
  }

  def merge(e1: Expr, e2: Expr)(implicit symbols: Symbols): Option[(Expr, Seq[(Variable, KnownValue)])] = {
    None
  }

  object Lens extends SemanticLens {
    def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
      out.simplifiedExpr match {
        case TreeModification.Goal(_, modified, index) =>
          in.expr match {
            case l@ADT(ADTType(adtid, tps), args) =>
              //val newOriginal = Lambda(Seq(x), lambdaArgs(i))
              for {pf <- repair(in.subExpr(args(index)), out.subExpr(modified))} yield {
                pf.wrap(x => ADT(l.adt, args.take(index) ++ List(x) ++ args.drop(index + 1)))
              }
            case _ => Stream.empty
          }
        case _ => Stream.empty
      }
    }
    isPreemptive = true
  }

  val Goal = TreeModificationGoal

  def apply(original: Expr, modified: Expr, argsInSequence: List[Identifier])(implicit symbols: Symbols): ProgramFormula = {
    ProgramFormula(Goal(original, modified, argsInSequence))
  }
  def apply(original: Expr, modified: Expr, next: Int)(implicit symbols: Symbols): ProgramFormula = {
    ProgramFormula(Goal(original, modified, next))
  }
  def unapply(pf: ProgramFormula)(implicit symbols: Symbols): Option[(Lambda, Expr, Int)] =
    Goal.unapply(pf.expr)

  object All {
    def unapply(pf: ProgramFormula)(implicit symbols: Symbols): Option[(Lambda, Expr, List[Int])] =
      Goal.All.unapply(pf.expr)
    def apply(original: Expr, modified: Expr, indices: List[Int])(implicit symbols: Symbols) =
      ProgramFormula(Goal.All.apply(original, modified, indices))
  }
}
