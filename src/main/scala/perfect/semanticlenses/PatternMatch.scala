package perfect
package semanticlenses

import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.ProgramFormula.{CloneTextMultiple, CustomProgramFormula, MergeProgramFormula}
import perfect.ReverseProgram.{Cache, maybeEvalWithCache, repair}
import perfect.StringConcatExtended._
import perfect.lenses.FunDefGoal

/**
  * Created by Mikael on 04/05/2017.
  */
object PatternMatch extends CustomProgramFormula with MergeProgramFormula {
  object Eval {
    def unapply(e: Expr)(implicit symbols: Symbols): Option[Expr] = e match {
      case PatternMatch.Goal(before, variables, forClone) =>
        Some(exprOps.replaceFromSymbols(variables.toMap, before))
      case _ => None
    }
  }
  def merge(e1: Expr, e2: Expr)(implicit symbols: Symbols): Option[(Expr, Seq[(Variable, KnownValue)])] = {
    e2 match {
      case PatternMatch.Goal(before, variables, forClone) =>
        e1 match {
          case CloneTextMultiple.Goal(left2, textVarRight2) =>
            e2 match {
              case CloneTextMultiple.Goal(left1, textVarRight1) =>
                CloneTextMultiple.Goal.merge(left1, textVarRight1, left2, textVarRight2)
              case _ => None
            }

          case PatternMatch.Goal(before2, variables2, forClone2) =>
            PatternMatch.Goal.merge(before, variables, forClone, before2, variables2, forClone2)
          case _ => None
        }
      case _ => None
    }
  }

  object Lens extends SemanticLens {
    override def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
      out.simplifiedExpr match {
        case PatternMatch.Goal(pattern, variables, forClone) =>
          in.expr match {
            case l: Literal[_] =>
              pattern match {
                case lPattern: Literal[_] =>
                  Stream(ProgramFormula(pattern))
                case vPattern: Variable =>
                  val value = variables.collectFirst{
                    case (v, value) if v == vPattern => value
                  }
                  value.toStream.map(value =>
                    ProgramFormula(pattern, Formula(vPattern -> InsertVariable(value)))
                  )
                case StringConcat(a, b) =>
                  val newFormula = Formula(exprOps.variablesOf(pattern).map(v => v -> InsertVariable(variables.collectFirst{
                    case (v2, value) if v2 == v => value
                  }.get)).toMap)
                  Stream(ProgramFormula(pattern, newFormula))
                case op => Log("[Internal error] Operation not supported in pattern matching: " + op)
                  Stream.empty
              }
            case StringConcat(expr1, expr2) =>
              pattern match {
                case StringConcats.Exhaustive(patterns) =>
                  val values: List[String] = patterns.map{ pattern =>
                    val StringLiteral(a) = ProgramFormula(pattern, Formula(variables.map{
                      case (v, value) => v -> StrongValue(value)}.toMap )).functionValue
                    a
                  }
                  val Some(StringLiteral(originalLeft)) = maybeEvalWithCache(in.formula.assignments.get(expr1))
                  val Some(StringLiteral(originalRight)) = maybeEvalWithCache(in.formula.assignments.get(expr2))
                  val shortestTailForLeft = values.inits.toList.reverse.find{
                    case l => l.mkString("").startsWith(originalLeft)
                  }.get
                  val coverage = shortestTailForLeft.mkString("")
                  if(coverage == originalLeft) {
                    val newLeftPattern = StringConcats(patterns.take(shortestTailForLeft.length))
                    val newRightPattern = StringConcats(patterns.drop(shortestTailForLeft.length))
                    val arguments = List(
                      repair(in.subExpr(expr1), out.subExpr(PatternMatch.Goal(newLeftPattern, variables, forClone))),
                      repair(in.subExpr(expr2), out.subExpr(PatternMatch.Goal(newRightPattern, variables, forClone))))
                    for{ regroupped <- ProgramFormula.regroupArguments(arguments)
                         (Seq(newLeft1, newLeft2), formula) = regroupped
                    } yield {
                      ProgramFormula(StringConcat(newLeft1, newLeft2), formula)
                    }
                  } else {
                    Log(s"coverage: `$coverage`")
                    Log(s"origleft: `$originalLeft`")
                    // shortestTailForLeft contains the originalLeft. We need to split the last variable.
                    val lastValue: String = values(shortestTailForLeft.length-1)
                    val extra = lastValue.length - (coverage.length - originalLeft.length) // > 0
                    patterns(shortestTailForLeft.length - 1) match {
                      case s: StringLiteral => // We can just split the string literal into two.
                        repair(in, PatternMatch(StringConcats(
                          patterns.take(shortestTailForLeft.length - 1) ++
                            List(StringLiteral(lastValue.substring(0, extra)),
                              StringLiteral(lastValue.substring(extra))) ++
                            patterns.drop(shortestTailForLeft.length)
                        ), variables, forClone))
                      case lastVar: Variable => // Way interesting, we need to split the variable
                        val leftVar = Variable(FreshIdentifier(Utils.uniqueName(lastVar.id.name, Set(lastVar.id.name))), StringType, Set())
                        val rightVar = Variable(FreshIdentifier(Utils.uniqueName(lastVar.id.name, Set(lastVar.id.name, leftVar.id.name))), StringType, Set())
                        val newFormula = Formula(Map(
                          lastVar -> InsertVariable(leftVar +& rightVar),
                          leftVar -> InsertVariable(StringLiteral(lastValue.substring(0, extra))),
                          rightVar -> InsertVariable(StringLiteral(lastValue.substring(extra)))))
                        val newLeftPattern = StringConcats(
                          patterns.take(shortestTailForLeft.length - 1) ++
                            List(leftVar))
                        val newRightPattern = StringConcats(List(rightVar) ++
                          patterns.drop(shortestTailForLeft.length)
                        )

                        val newVariables = variables.filter(_._1 != lastVar) ++
                          List((leftVar, StringLiteral(lastValue.substring(0, extra))),
                            (rightVar, StringLiteral(lastValue.substring(extra))))

                        val arguments = List(
                          repair(in.subExpr(expr1), out.subExpr(PatternMatch.Goal(newLeftPattern, newVariables, forClone))),
                          repair(in.subExpr(expr2), out.subExpr(PatternMatch.Goal(newRightPattern, newVariables, forClone))))
                        for{ regroupped <- ProgramFormula.regroupArguments(arguments)
                             (Seq(newLeft1, newLeft2), formula) = regroupped
                        } yield {
                          ProgramFormula(StringConcat(newLeft1, newLeft2), formula combineWith newFormula)
                        }

                      case e => throw new Exception(s"[internal error] Only variables and strings in string patterns, got $e")
                    }
                  }
              }
            case ADT(adtType@ADTType(tp, tpArgs), argsIn) =>
              pattern match {
                case ADT(adtType2, argsIn2) if adtType2 == adtType =>
                  val argumentsRepaired = for{ (argIn, argIn2) <- argsIn.zip(argsIn2) } yield {
                    repair(in.subExpr(argIn), out.subExpr(
                      PatternMatch.Goal(
                        argIn2, variables, forClone
                      )
                    )
                    )
                  }
                  for{ res <- ProgramFormula.regroupArguments(argumentsRepaired)
                       (newArgs, formula) = res
                  } yield {
                    ProgramFormula(ADT(adtType, newArgs), formula)
                  }

                case v: Variable if variables.indexWhere(_._1 == v) >= 0 =>
                  val value = variables.collectFirst{ case (`v`, value) => value  }.get
                  // Normally the value equals functionValue, so no need to call it.
                  Stream(ProgramFormula(v, Formula(v -> InsertVariable(value))))

                case _ => throw new Exception("Did not expect something else than an ADT of same type or variable here")
              }

            case e =>
              Log(s"[Internal warning] PatternMatch not supported on $e")
              Stream.empty // f
          }

        case _ => Stream.empty // Not pattern matching.
      }
    }
    isPreemptive = true
  }


  def apply(before: Expr, variables: List[(Variable, Expr)], forClone: Boolean)(implicit symbols: Symbols) =
  ProgramFormula(Goal(before, variables, forClone))
  def unapply(e: ProgramFormula)(implicit symbols: Symbols): Option[(Expr, List[(Variable, Expr)], Boolean)] = {
    Goal.unapply(e.expr)
  }

  object Goal extends FunDefGoal {
    import ImplicitTuples._
    private val PMId = FreshIdentifier("matcher")

    def merge(before1: Expr, variables1: List[(Variable, Expr)], forClone1: Boolean,
              before2: Expr, variables2: List[(Variable, Expr)], forClone2: Boolean, insertedVariables: Set[Variable] = Set())(implicit symbols: Symbols): Option[(Expr, Seq[(Variable, KnownValue)])] = {
      ???
    }

    def Build(names: (ValDef, Expr)*)(f: Seq[Variable] => Expr)(implicit symbols: Symbols): Expr = {
      val variables = names.toList.map(n => n._1.toVariable)
      val before = f(variables)
      apply(before, variables.zip(names.map(_._2)), true)
    }

    def apply(before: Expr, variables: List[(Variable, Expr)], forClone: Boolean)(implicit symbols: Symbols) : Expr = {
      E(PMId)(before.getType)(Application(
        Lambda(variables.map(_._1.toVal), before)
        , variables.map(_._2)), BooleanLiteral(forClone))
    }

    def unapply(e: Expr)(implicit symbols: Symbols): Option[(Expr, List[(Variable, Expr)], Boolean)] = {
      e match {
        case FunctionInvocation(PMId, Seq(_), Seq(
        Application(Lambda(valdefs, before), varValues),
        BooleanLiteral(forClone)
        )) =>
          Some((before, valdefs.toList.map(_.toVariable).zip(varValues), forClone))
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
}