package perfect.lenses
import inox.{FreshIdentifier, Identifier, trees, _}
import perfect.InoxProgramUpdater
import perfect.semanticlenses.TreeWrap
import inox.trees._
import inox.trees.dsl._
import perfect.StringConcatExtended._

/**
  * Created by Mikael on 09/05/2017.
  */
trait PatternReplaceLenses { self: InoxProgramUpdater.type =>
  object PatternReplaceLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: trees.Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case PatternReplaceGoal(pattern, variables, after) =>
          in.exp match {
            case ADT(adtType@ADTType(tp, tpArgs), argsIn) =>
              pattern match { // TODO: Pattern replace at higher level?
                case ADT(adtType2, argsIn2) if adtType2 == adtType =>
                  val argsMatched = argsIn.zip(argsIn2).map{
                    case (expr, pattern) =>
                      repair(
                        in.subExpr(expr),
                        out.subExpr(
                          PatternReplaceGoal(
                            pattern, variables, ExpFalse
                          )))
                  }
                  for{ argumentsCombined <-ContExp.regroupArguments(argsMatched)
                       (_, context) = argumentsCombined
                  } yield ContExp(after, context)

                case v: Variable =>
                  Stream.empty

                case _ =>
                  //throw new Exception("Did not expect something else than an ADT of same type or variable here")
                  Stream.empty
              }
            case _ => Stream.empty
          }
        case _ => Stream.empty
      }
    }
    isPreemptive = true
  }
}

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