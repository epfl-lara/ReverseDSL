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

  object CloneTextMultiple {
    def apply(left: String, textVarRights: List[(String, Variable, String)])(implicit symbols: Symbols) = {
      val before = ((StringLiteral(left): Expr) /: textVarRights) {
        case (e: Expr, (middle, v, right)) => e +<>& v +<>& StringLiteral(right)
      }
      PatternMatchGoal(before, textVarRights.map(x => x._2 -> StringLiteral(x._1)), true)
    }
    def unapply(e: Expr)(implicit symbols: Symbols): Option[(String, List[(String, Variable, String)])] = e match {
      case PatternMatchGoal(StringConcats.Exhaustive(strs), variables, true) =>
        def getVarValue(v: Variable): String = variables.collectFirst {
          case (v2, StringLiteral(s)) if v2 == v => s
        }.get

        def unbuild(e: List[Expr]): Option[(String, List[(String, Variable, String)])] = e match {
          case Nil => Some(("", Nil))
          case StringLiteral(text) :: tail => unbuild(tail).map{ case (left, l) =>
            ((text+left), l)
          }
          case (v: Variable)::tail => unbuild(tail).map{ case (left, l) =>
            ("", (getVarValue(v), v, left)::l)
          }
          case _ => None
        }
        unbuild(strs)
      case _ => None
    }

    private def SplitVar(v1: Variable, inserted: Set[Variable]): (Variable, Variable) = {
      val v1p1 = Variable(FreshIdentifier(perfect.Utils.uniqueName(v1.id.name, inserted.map(_.id.name) + v1.id.name)), StringType, Set())
      val v1p2 = Variable(FreshIdentifier(perfect.Utils.uniqueName(v1.id.name, inserted.map(_.id.name) + v1.id.name + v1p1.id.name)), StringType, Set())
      (v1p1, v1p2)
    }
    /*def merge(left1: String, textVarRight1: List[(String, Variable, String)],
              left2: String, textVarRight2: List[(String, Variable, String)], inserted: Set[Variable] = Set())(implicit symbols: Symbols): Option[(Expr, Seq[(Variable, KnownValue)])] = {
      Log(s"merge with inserted ${inserted}\n1. ($left1, $textVarRight1)\n2. ($left2, $textVarRight2)")
      if(left1.length > 0 && left2.length > 0) {
        if(left1.length <= left2.length) {
          assert(left2.startsWith(left1))
          merge("", textVarRight1,
            left2.substring(0, left1.length), textVarRight2, inserted).map{
            case (Goal(newLeft1, newTextVarRight1), vk) =>
              (Goal(left1 + newLeft1, newTextVarRight1), vk)
          }
        } else { // if(left1.length > left2.length)
          merge(left2, textVarRight2, left1, textVarRight1, inserted)
        }
      } else {
        // At least one of left1 and left2 is empty.
        (textVarRight1, textVarRight2) match {
          case (Nil, Nil) if left1 == left2 =>
            Some((apply(left1, Nil), Nil))
          case (Nil, textVarRight2) if left1.startsWith(left2) =>
            Some((apply(left2, textVarRight2), Nil))
          case (textVarRight1, Nil) if left2.startsWith(left1) =>
            Some((apply(left1, textVarRight1), Nil))
          case ((middle1, v1, right1) :: tail1, (middle2, v2, right2) :: tail2) =>
            if (left1.length == 0) {
              if (left2.startsWith(middle1)) {
                // We can insert the first variable in place of left2.
                val updatedLeft2 = left2.substring(middle1.length)
                val updatedRight1 = right1
                merge(updatedRight1, tail1, updatedLeft2, textVarRight2, inserted).map {
                  case (Goal(leftNew, textVarRightNew), mp) =>
                    (Goal(left1, (middle1, v1, leftNew) :: textVarRightNew), mp)
                }
              } else if(left2.length == 0) { // Overlapping between variables
                if(middle1.length == middle2.length) {
                  if(inserted(v1)) {
                    if(inserted(v2)) {
                      Log("[internal warning] tried to merge two inserted variables, makes no sense.")
                      None
                    } else {
                      merge(right1, tail1, right2, tail2, inserted) map {
                        case (Goal(leftNew, textVarRightNew), mp) =>
                          (Goal("", (middle1, v1, leftNew)::textVarRightNew),
                            (v2 -> InsertVariable(v1)) +: mp)
                      }
                    }
                  } else {
                    if(inserted(v2)) {
                      merge(left2, textVarRight2, left1, textVarRight1, inserted)
                    } else { // We insert a new variable and link the two other variables.
                      val v = CloneText.Var(v1.id.name, Seq(v2.id.name))
                      merge(right1, tail1, right2, tail2, inserted) map {
                        case (Goal(leftNew, textVarRightNew), mp) =>
                          (Goal("", (middle1, v, leftNew)::textVarRightNew),
                            (v1 -> InsertVariable(v)) +: (v2 -> InsertVariable(v)) +: mp)
                      }
                    }
                  }
                } else if(middle1.length < middle2.length) {
                  if(inserted(v1)) {
                    if(inserted(v2)) {
                      Log("[internal warning] tried to merge two inserted variables, makes no sense.")
                      None
                    } else {
                      // We split v2 into a second variable.
                      val (_, v2p2) = SplitVar(v2, inserted)
                      val news = v2 -> InsertVariable(v1 +& v2p2)
                      val positionSplit = middle1.length
                      val newMiddle2 = middle2.substring(positionSplit)
                      merge(right1, tail1, "", (newMiddle2, v2p2, right2)::tail2, inserted) map {
                        case (Goal(leftNew, textVarRightNew), mp) =>
                          (Goal("", (middle1, v1, leftNew)::textVarRightNew), news +: mp)
                      }
                    }
                  } else {
                    val (v2p1, v2p2) = SplitVar(v2, inserted)
                    val news = v2 -> InsertVariable(v2p1 +& v2p2)
                    val position = middle1.length
                    val middle21 = middle2.substring(0, position)
                    val middle22 = middle2.substring(position)
                    merge(left1, textVarRight1,
                      left2, (middle21, v2p1, "") :: (middle22, v2p2, right2) :: tail2, inserted ++ Seq(v2p1, v2p2)
                    ) map {
                      case (ctm, mp) => (ctm, news +: mp)
                    }
                  }
                } else {
                  merge(left2, textVarRight2, left1, textVarRight1, inserted)
                }
              } else { // Partial overlapping of a variable on the left string of the next.
                assert(middle1.startsWith(left2)) // We need to introduce one variable for the overlap.
                val (v1p1, v1p2) = SplitVar(v1, inserted)
                val news = v1 -> InsertVariable(v1p1 +& v1p2)
                val positionSplit = left2.length
                val newMiddle1 = middle1.substring(0, positionSplit) // should equal left2.
                val newLeft1 = middle1.substring(positionSplit)

                merge(left1, (newMiddle1, v1p1, "") :: (newLeft1, v1p2, right1) :: tail1,
                  left2, textVarRight2, inserted ++ Seq(v1p1, v1p2)
                ).map {
                  case (ctm, mp) =>
                    (ctm, news +: mp)
                }
              }
            } else { //if (left2.length == 0)
              merge(left2, textVarRight2, left1, textVarRight1, inserted)
            }
        }
      }
    } /: Log.prefix(s"merge with inserted ${inserted}\n1. ($left1, $textVarRight1)\n2. ($left2, $textVarRight2) =\n")*/
  }
}