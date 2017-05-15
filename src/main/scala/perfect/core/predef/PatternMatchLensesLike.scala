package perfect.core
package predef


/**
  * Created by Mikael on 15/05/2017.
  */
trait PatternMatchLensesLike { self: ProgramUpdater
  with ContExps with Lenses with StringLenses with StringConcatLenses with ADTLenses =>
  trait PatternMatchLensGoalExtractor {
    def unapply(e: Exp): Option[(Exp, List[(Var, Exp)], Boolean)]
    def apply(pattern: Exp, vars: List[(Var, Exp)], forClone: Boolean): Exp
  }

  class PatternMatchLensLike(PatternMatchLensGoal: PatternMatchLensGoalExtractor) extends SemanticLens {
    override def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case PatternMatchLensGoal(pattern, variables, forClone) =>
          in.exp match {
            case l if isValue(l) =>
              pattern match {
                case lPattern if isValue(lPattern) =>
                  Stream(ContExp(pattern))
                case Var(vPattern) =>
                  val value = variables.collectFirst{
                    case (v, inner_value) if v == vPattern => inner_value
                  }
                  value.toStream.map(value =>
                    ContExp(pattern, Cont(vPattern -> InsertVariable(value)))
                  )
                case _ =>
                  val newFormula = Cont(freeVariables(pattern).map(v => v -> InsertVariable(variables.collectFirst{
                    case (v2, value) if v2 == v => value
                  }.get)).toMap)
                  Stream(ContExp(pattern, newFormula))
              }
            case StringConcat(expr1, expr2) =>
              pattern match {
                case StringConcat.Exhaustive(patterns) =>
                  val values: List[String] = patterns.map{ pattern =>
                    val StringLiteral(a) = ContExp(pattern, Cont(variables.map{
                      case (v, value) => v -> StrongValue(value)}.toMap )).functionValue
                    a
                  }
                  val Some(StringLiteral(originalLeft)) = maybeEvalWithCache(in.context.assignments.get(expr1))
                  val Some(StringLiteral(originalRight)) = maybeEvalWithCache(in.context.assignments.get(expr2))
                  val shortestTailForLeft = values.inits.toList.reverse.find(l => l.mkString("").startsWith(originalLeft)).getOrElse(return Stream.empty)
                  val coverage = shortestTailForLeft.mkString("")
                  if(coverage == originalLeft) {
                    val newLeftPattern = StringConcat.Multiple(patterns.take(shortestTailForLeft.length))
                    val newRightPattern = StringConcat.Multiple(patterns.drop(shortestTailForLeft.length))
                    val arguments = List(
                      repair(in.subExpr(expr1), out.subExpr(PatternMatchLensGoal(newLeftPattern, variables, forClone))),
                      repair(in.subExpr(expr2), out.subExpr(PatternMatchLensGoal(newRightPattern, variables, forClone))))
                    for{ regroupped <- ContExp.regroupArguments(arguments)
                         (Seq(newLeft1, newLeft2), context) = regroupped
                    } yield {
                      ContExp(StringConcat(newLeft1, newLeft2), context)
                    }
                  } else {
                    //Log(s"coverage: `$coverage`")
                    //Log(s"origleft: `$originalLeft`")
                    // shortestTailForLeft contains the originalLeft. We need to split the last variable.
                    val lastValue: String = values(shortestTailForLeft.length-1)
                    val extra = lastValue.length - (coverage.length - originalLeft.length) // > 0
                    patterns(shortestTailForLeft.length - 1) match {
                      case s@StringLiteral(_) => // We can just split the string literal into two.
                        repair(in, out.subExpr(PatternMatchLensGoal(StringConcat.Multiple(
                          patterns.take(shortestTailForLeft.length - 1) ++
                            List(StringLiteral(lastValue.substring(0, extra)),
                              StringLiteral(lastValue.substring(extra))) ++
                            patterns.drop(shortestTailForLeft.length)
                        ), variables, forClone)))
                      case Var(lastVar) => // Way interesting, we need to split the variable
                        val leftVar = freshen(lastVar, lastVar)
                        val rightVar = freshen(lastVar, lastVar, leftVar)
                        val newFormula = Cont(Map(
                          lastVar -> InsertVariable(leftVar +& rightVar),
                          leftVar -> InsertVariable(StringLiteral(lastValue.substring(0, extra))),
                          rightVar -> InsertVariable(StringLiteral(lastValue.substring(extra)))))
                        val newLeftPattern = StringConcat.Multiple(
                          patterns.take(shortestTailForLeft.length - 1) ++
                            List(leftVar))
                        val newRightPattern = StringConcat.Multiple(List(rightVar) ++
                          patterns.drop(shortestTailForLeft.length)
                        )

                        val newVariables = variables.filter(_._1 != lastVar) ++
                          List((leftVar, StringLiteral(lastValue.substring(0, extra))),
                            (rightVar, StringLiteral(lastValue.substring(extra))))

                        val arguments = List(
                          repair(in.subExpr(expr1), out.subExpr(PatternMatchLensGoal(newLeftPattern, newVariables, forClone))),
                          repair(in.subExpr(expr2), out.subExpr(PatternMatchLensGoal(newRightPattern, newVariables, forClone))))
                        for{ regroupped <- ContExp.regroupArguments(arguments)
                             (Seq(newLeft1, newLeft2), context) = regroupped
                        } yield {
                          ContExp(StringConcat(newLeft1, newLeft2), context combineWith newFormula)
                        }

                      case e => throw new Exception(s"[internal error] Only variables and strings in string patterns, got $e")
                    }
                  }
              }
            case inExp@ADT(argsIn, adtBuilder) =>
              pattern match {
                case ADT(argsIn2, adtBuilder2) if isSameADT(inExp, pattern) =>
                  val argumentsRepaired = for{ (argIn, argIn2) <- argsIn.zip(argsIn2) } yield {
                    repair(in.subExpr(argIn), out.subExpr(
                      PatternMatchLensGoal(argIn2, variables, forClone)
                    )
                    )
                  }
                  for{ res <- ContExp.regroupArguments(argumentsRepaired)
                       (newArgs, context) = res
                  } yield {
                    ContExp(adtBuilder(newArgs), context)
                  }

                case Var(v) if variables.indexWhere(_._1 == v) >= 0 =>
                  val value = variables.collectFirst{ case (`v`, inner_value) => inner_value  }.get
                  // Normally the value equals functionValue, so no need to call it.
                  Stream(ContExp(v, Cont(v -> InsertVariable(value))))

                case _ => Stream.empty
                  //throw new Exception("Did not expect something else than an ADT of same type or variable here")
              }

            case e =>
              //Log(s"[Internal warning] PatternMatch not supported on $e")
              Stream.empty // f
          }

        case _ => Stream.empty // Not pattern matching.
      }
    }
    isPreemptive = true
  }
}
