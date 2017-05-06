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
object PatternReplace extends CustomProgramFormula {
  object Eval {
    def unapply(e: Expr)(implicit symbols: Symbols): Option[Expr] = e match {
      case Expr(before, variables, after) =>
        Some(exprOps.replaceFromSymbols(variables.map{ case (k, v) => k.toVal -> v}.toMap, after))
      case _ => None
    }
  }
  def merge(e1: Expr, e2: Expr)(implicit symbols: Symbols): Option[(Expr, Seq[(Variable, KnownValue)])] = {
    e1 match { case Expr(before, variables, after) =>
      e2 match { case Expr(before2, variables2, after2) =>
        Log(s"[internal warning]: Merge of two pattern replace not supported $e1, $e2")
        None
      case _ => None
      }
    case _ => None
    }
  }


  object Lens extends SemanticLens {
    override def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
      out.simplifiedExpr match {
        case PatternReplace.Expr(pattern, variables, after) =>
          in.expr match {
            case ADT(adtType@ADTType(tp, tpArgs), argsIn) =>
              pattern match { // TODO: Pattern replace at higher level?
                case ADT(adtType2, argsIn2) if adtType2 == adtType =>
                  val argsMatched = argsIn.zip(argsIn2).map{
                    case (expr, pattern) =>
                      repair(
                        in.subExpr(expr),
                        out.subExpr(
                          PatternMatch.Expr(
                            pattern, variables, false
                          )))
                  }
                  for{ argumentsCombined <-ProgramFormula.regroupArguments(argsMatched)
                       (_, formula) = argumentsCombined
                  } yield ProgramFormula(after, formula)

                case v: Variable =>
                  ???

                case _ => throw new Exception("Did not expect something else than an ADT of same type or variable here")
              }
            case _ => Stream.empty
          }
        case _ => Stream.empty
      }
    }
    isPreemptive = true
  }

  private val PMId = FreshIdentifier("replace")

  def apply(before: Expr, variables: List[(Variable, Expr)], after: Expr)(implicit symbols: Symbols) =
    ProgramFormula(Expr(before, variables, after))
  def unapply(e: ProgramFormula)(implicit symbols: Symbols): Option[(Expr, List[(Variable, Expr)], Expr)] = {
    Expr.unapply(e.expr)
  }

  object Expr {
    import ImplicitTuples._

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
  }

  def funDef = mkFunDef(PMId)("A"){ case Seq(tA) =>
    (Seq("id"::tA), tA,
      { case Seq(id) =>
        id // Dummy
      })
  }
}
