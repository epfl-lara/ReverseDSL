package perfect.lenses
import inox.{FreshIdentifier, Identifier}
import perfect.InoxProgramUpdater
import perfect.semanticlenses.TreeWrap
import inox.trees._
import inox._
import inox.trees.dsl._
import perfect.StringConcatExtended._

/**
  * Created by Mikael on 09/05/2017.
  */
trait PatternMatchLenses { self: InoxProgramUpdater.type =>
  object PatternMatchLens extends SemanticLens {
    override def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case PatternMatchGoal(pattern, variables, forClone) =>
          in.exp match {
            case l: Literal[_] =>
              pattern match {
                case lPattern: Literal[_] =>
                  Stream(ContExp(pattern))
                case vPattern: Variable =>
                  val value = variables.collectFirst{
                    case (v, value) if v == vPattern => value
                  }
                  value.toStream.map(value =>
                    ContExp(pattern, Cont(vPattern -> InsertVariable(value)))
                  )
                case StringConcat(a, b) =>
                  val newFormula = Cont(exprOps.variablesOf(pattern).map(v => v -> InsertVariable(variables.collectFirst{
                    case (v2, value) if v2 == v => value
                  }.get)).toMap)
                  Stream(ContExp(pattern, newFormula))
                case op => //Log("[Internal error] Operation not supported in pattern matching: " + op)
                  Stream.empty
              }
            case StringConcat(expr1, expr2) =>
              pattern match {
                case StringConcats.Exhaustive(patterns) =>
                  val values: List[String] = patterns.map{ pattern =>
                    val StringLiteral(a) = ContExp(pattern, Cont(variables.map{
                      case (v, value) => v -> StrongValue(value)}.toMap )).functionValue
                    a
                  }
                  val Some(StringLiteral(originalLeft)) = maybeEvalWithCache(in.context.assignments.get(expr1))
                  val Some(StringLiteral(originalRight)) = maybeEvalWithCache(in.context.assignments.get(expr2))
                  val shortestTailForLeft = values.inits.toList.reverse.find{
                    case l => l.mkString("").startsWith(originalLeft)
                  }.get
                  val coverage = shortestTailForLeft.mkString("")
                  if(coverage == originalLeft) {
                    val newLeftPattern = StringConcats(patterns.take(shortestTailForLeft.length))
                    val newRightPattern = StringConcats(patterns.drop(shortestTailForLeft.length))
                    val arguments = List(
                      repair(in.subExpr(expr1), out.subExpr(PatternMatchGoal(newLeftPattern, variables, forClone))),
                      repair(in.subExpr(expr2), out.subExpr(PatternMatchGoal(newRightPattern, variables, forClone))))
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
                      case s: StringLiteral => // We can just split the string literal into two.
                        repair(in, out.subExpr(PatternMatchGoal(StringConcats(
                          patterns.take(shortestTailForLeft.length - 1) ++
                            List(StringLiteral(lastValue.substring(0, extra)),
                              StringLiteral(lastValue.substring(extra))) ++
                            patterns.drop(shortestTailForLeft.length)
                        ), variables, forClone)))
                      case lastVar: Variable => // Way interesting, we need to split the variable
                        val leftVar = freshen(lastVar, lastVar)
                        val rightVar = freshen(lastVar, lastVar, leftVar)
                        val newFormula = Cont(Map(
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
                          repair(in.subExpr(expr1), out.subExpr(PatternMatchGoal(newLeftPattern, newVariables, forClone))),
                          repair(in.subExpr(expr2), out.subExpr(PatternMatchGoal(newRightPattern, newVariables, forClone))))
                        for{ regroupped <- ContExp.regroupArguments(arguments)
                             (Seq(newLeft1, newLeft2), context) = regroupped
                        } yield {
                          ContExp(StringConcat(newLeft1, newLeft2), context combineWith newFormula)
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
                      PatternMatchGoal(
                        argIn2, variables, forClone
                      )
                    )
                    )
                  }
                  for{ res <- ContExp.regroupArguments(argumentsRepaired)
                       (newArgs, context) = res
                  } yield {
                    ContExp(ADT(adtType, newArgs), context)
                  }

                case v: Variable if variables.indexWhere(_._1 == v) >= 0 =>
                  val value = variables.collectFirst{ case (`v`, value) => value  }.get
                  // Normally the value equals functionValue, so no need to call it.
                  Stream(ContExp(v, Cont(v -> InsertVariable(value))))

                case _ => throw new Exception("Did not expect something else than an ADT of same type or variable here")
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


object PatternMatchGoal extends FunDefGoal {
  private val PMId = FreshIdentifier("matcher")

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