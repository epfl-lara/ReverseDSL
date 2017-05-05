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
  object Lens extends SemanticLens {
    def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
      out.simplifiedExpr match {
      case TreeUnwrap.Expr(tpe, original, l) =>
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

  private val Unwrap = FreshIdentifier("unwrap")

  def apply(tpe: Type, original: Expr, argsInSequence: List[Identifier]): ProgramFormula = {
    ProgramFormula(Expr(tpe, original, argsInSequence))
  }
  def unapply(pf: ProgramFormula): Option[(Type, Expr, List[Identifier])] = {
    Expr.unapply(pf.expr)
  }
  object Expr {
    def apply(tpe: Type, original: Expr, argsInSequence: List[Identifier]): Expr = {
      E(Unwrap)(tpe)(original, Select(tpe, argsInSequence))
    }
    def unapply(e: Expr): Option[(Type, Expr, List[Identifier])] = {
      e match {
        case FunctionInvocation(Unwrap, Seq(tpe), Seq(original, Lambda(Seq(unwrapvd), adtselectors))) =>
          def unbuild(e: Expr): (Type, Expr, List[Identifier]) = e match {
            case ADTSelector(e, i) =>
              val (t, res, l) = unbuild(e)
              (t, res, l :+ i)
            case res => (tpe, original, Nil)
          }
          Some(unbuild(adtselectors))
        case _ => None
      }
    }
  }

  /** Builds and Unbuilds a lambda to select parts of the expression */
  object Select {
    def apply(tpe: Type, argsInSequence: List[Identifier]): Expr = {
      \("original"::tpe)(original =>
        ((original: Expr) /: argsInSequence){ case (e, i) => ADTSelector(e, i)}
      )
    }
    def unapply(e: Expr): Option[(Type, List[Identifier])] = {
      e match {
        case Lambda(Seq(ValDef(_, tpe, _)), body) =>
          def unbuild(e: Expr): Option[(Type, List[Identifier])] = e match {
            case ADTSelector(e, i) => unbuild(e) map { case (t, l) => (t, l :+ i) }
            case v: Variable => Some((tpe, Nil))
            case _ => None
          }
          unbuild(body)
        case _ => None
      }
    }
  }

  def funDef = mkFunDef(Unwrap)("A"){ case Seq(tA) =>
    (Seq("original"::tA, "unwrapper"::FunctionType(Seq(tA), tA)),
      tA, {
      case Seq(original, unwrapper) =>
        Application(unwrapper, Seq(original))
    })
  }
}

