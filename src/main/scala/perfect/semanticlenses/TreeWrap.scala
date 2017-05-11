package perfect
package semanticlenses

import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.ProgramFormula.CustomProgramFormula
import perfect.ReverseProgram.{Cache, maybeEvalWithCache, repair}

/**
  * Created by Mikael on 05/05/2017.
  */

/** The tree is included in the new output */
object TreeWrap extends CustomProgramFormula {
  object Eval {
    def unapply(arg: Expr)(implicit symbols: Symbols): Option[Expr] = arg match {
      case Goal(tree, wrapper) =>
        Some(wrapper(tree))
      case _ => None
    }
  }
  def merge(e1: Expr, e2: Expr)(implicit symbols: Symbols): Option[(Expr, Seq[(Variable, KnownValue)])] = {
    e1 match { case Goal(tree, wrapper) =>
      e2 match { case Goal(tree, wrapper) =>
        Log(s"[internal warning]: Merge of two Tree wrap not supported $e1, $e2")
        None
      case _ => None
      }
    case _ => None
    }
  }

  object Lens extends SemanticLens {
    def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
      out.simplifiedExpr match {
      case TreeWrapGoal(original, wrapper) if in.canDoWrapping =>
        in.expr match {
          case l: Let => Stream.empty
          case Application(Lambda(_, _), _) => Stream.empty
          case _ => Stream(ProgramFormula(wrapper(in.expr), out.formula))
        }
      case _ => Stream.empty
      }
    }
    isPreemptive = true
  }

  def apply(tree: Expr, wrapper: Expr => Expr)(implicit symbols: Symbols): ProgramFormula = {
    ProgramFormula(Goal.apply(tree, wrapper))
  }
  def unapply(pf: ProgramFormula)(implicit symbols: Symbols): Option[(Expr, Expr => Expr)] = {
    Goal.unapply(pf.expr)
  }

  val Goal = TreeWrapGoal
}
