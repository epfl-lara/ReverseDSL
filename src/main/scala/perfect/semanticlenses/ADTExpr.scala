package perfect
package semanticlenses

import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.ProgramFormula.CustomProgramFormula
import perfect.ReverseProgram.{Cache, maybeEvalWithCache, repair}
import perfect.StringConcatExtended._

/**
  * Created by Mikael on 04/05/2017.
  */
object ADTExpr extends CustomProgramFormula {
  object Eval {
    def unapply(e: Expr)(implicit symbols: Symbols) = e match {
      case e@ADT(_, _) => Some(e)
      case _ => None
    }
  }
  object Lens extends SemanticLens {
    override def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
      Stream.empty // TODO: Include ADT repair
    }
  }
  def merge(e1: Expr, e2: Expr): Option[(Expr, Seq[(Variable, KnownValue)])] = e2 match {
    case e2@ADT(tpe, vars1) if vars1.forall(_.isInstanceOf[Variable]) =>
      e1 match {
        case ADT(tpe2, vars2) if vars2.forall(_.isInstanceOf[Variable]) && tpe == tpe2 =>
          val vvars1: Seq[Variable] = vars1.collect { case v: Variable => v }
          val vvars2: Seq[Variable] = vars2.collect { case v: Variable=> v }
          Some((e1, vars1.zip(vvars2).map{ case (x1: Variable, x2: Variable) =>
              x1 -> StrongValue(x2)
          }))
        case _ => None
      }
  }

  def funDef = mkFunDef(FreshIdentifier("ADT"))("A"){ case Seq(tA) =>
    (Seq("id"::tA), tA,
      { case Seq(id) =>
        id // Dummy
      })
  }
}
