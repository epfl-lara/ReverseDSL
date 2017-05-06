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
/** The tree is included in the new output */
object TreeWrap extends CustomProgramFormula {
  object Eval {
    def unapply(arg: Expr)(implicit symbols: Symbols): Option[Expr] = arg match {
      case Expr(tree, wrapper) =>
        Some(wrapper(tree))
      case _ => None
    }
  }
  object Lens extends SemanticLens {
    def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
      out.simplifiedExpr match {
      case TreeWrap.Expr(original, wrapper) if in.canDoWrapping =>
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

  private val Wrap = FreshIdentifier("wrap")
  def apply(tree: Expr, wrapper: Expr => Expr)(implicit symbols: Symbols): ProgramFormula = {
    ProgramFormula(Expr.apply(tree, wrapper))
  }
  def unapply(pf: ProgramFormula)(implicit symbols: Symbols): Option[(Expr, Expr => Expr)] = {
    Expr.unapply(pf.expr)
  }
  object Expr {
    def apply(tree: Expr, wrapper: Expr => Expr)(implicit symbols: Symbols): Expr = {
      val tpe = tree.getType
      E(Wrap)(tpe)(\("tree"::tpe)(treeVar => wrapper(treeVar)), tree)
    }
    def unapply(expr: Expr)(implicit symbols: Symbols): Option[(Expr, Expr => Expr)] = {
      expr match {
        case FunctionInvocation(Wrap, tpe, Seq(Lambda(Seq(treeVal), wtree), original)) =>
          Some((original, (vr: Expr) => exprOps.replaceFromSymbols(Map(treeVal -> vr), wtree)))
        case _ => None
      }
    }
  }
  def funDef = mkFunDef(Wrap)("A"){ case Seq(tA) =>
    (Seq("wrapper"::FunctionType(Seq(tA), tA), "tree"::tA),
      tA, {
      case Seq(wrapper, tree) =>
        Application(wrapper, Seq(tree))
    })
  }
}
