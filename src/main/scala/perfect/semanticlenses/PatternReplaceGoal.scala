package perfect.semanticlenses

import perfect.lenses.FunDefGoal
import inox._
import inox.trees._
import inox.trees.dsl._

/**
  * Created by Mikael on 11/05/2017.
  */
object PatternReplaceGoal extends FunDefGoal {
  import perfect.ImplicitTuples._

  private val PMId = FreshIdentifier("replace")

  def Build(names: (ValDef, Expr)*)(f: Seq[Variable] => (Expr, Expr))(implicit symbols: Symbols): Expr = {
    val variables = names.toList.map(n => n._1.toVariable)
    val (before, after) = f(variables)
    apply(before, variables.zip(names.map(_._2)), after)
  }

  def apply(before: Expr, variables: List[(Variable, Expr)], after: Expr)(implicit symbols: Symbols) : Expr = {
    E(PMId)(after.getType)(Application(
      Lambda(variables.map(_._1.toVal), _Tuple2(before.getType, after.getType)(before, after).getField(_2))
      , variables.map(_._2)))
  }

  def unapply(e: Expr)(implicit symbols: Symbols): Option[(Expr, List[(Variable, Expr)], Expr)] = {
    e match {
      case FunctionInvocation(PMId, Seq(_), Seq(
      Application(Lambda(valdefs, ADTSelector(ADT(_, Seq(before, after)), `_2`)), varValues)
      )) =>
        Some((before, valdefs.toList.map(_.toVariable).zip(varValues), after))
      case _ => None
    }
  }

  def funDef = mkFunDef(PMId)("A"){ case Seq(tA) =>
    (Seq("id"::tA), tA,
      { case Seq(id) =>
        id // Dummy
      })
  }
}
