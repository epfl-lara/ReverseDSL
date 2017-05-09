package perfect.lenses
import inox.FreshIdentifier
import perfect.InoxProgramUpdater
import perfect.semanticlenses.TreeWrap
import inox.trees.{Application, Lambda, Let}

/**
  * Created by Mikael on 09/05/2017.
  */
trait TreeWrapLenses { self: InoxProgramUpdater.type =>
  object TreeWrapLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case TreeWrapGoal(original, wrapper) if in.canDoWrapping =>
          in.exp match {
            case l: Let => Stream.empty
            case Application(Lambda(_, _), _) => Stream.empty
            case _ => Stream(ContExp(wrapper(in.exp), out.context))
          }
        case _ => Stream.empty
      }
    }
    isPreemptive = true
  }
}



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