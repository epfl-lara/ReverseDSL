package perfect.semanticlenses

import inox._
import inox.trees._
import inox.trees.dsl._

/**
  * Created by Mikael on 11/05/2017.
  */
object TreeWrapGoal extends FunDefGoal {
  import inox.trees.{Expr, Symbols, dsl, FunctionInvocation, exprOps, FunctionType}
  import dsl._
  private val Wrap = FreshIdentifier("wrap")

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

  def funDef = mkFunDef(Wrap)("A"){ case Seq(tA) =>
    (Seq("wrapper"::FunctionType(Seq(tA), tA), "tree"::tA),
      tA, {
      case Seq(wrapper, tree) =>
        Application(wrapper, Seq(tree))
    })
  }
}
