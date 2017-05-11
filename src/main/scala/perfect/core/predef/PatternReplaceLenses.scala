package perfect.core.predef

import perfect.core._

/**
  * Created by Mikael on 09/05/2017.
  */
trait PatternReplaceLenses { self: ProgramUpdater with ContExps with Lenses with ADTLenses with PatternMatchLenses =>

  def extractPatternReplaceGoal(e: Exp): Option[(Exp, List[(Var, Exp)], Exp)]
  def buildPatternReplaceGoal(pattern: Exp, variables: List[(Var, Exp)], after: Exp): Exp

  object PatternReplaceLensGoal {
    def unapply(e: Exp) = extractPatternReplaceGoal(e)
    def apply(pattern: Exp, variables: List[(Var, Exp)], after: Exp) =
      buildPatternReplaceGoal(pattern, variables, after)
  }


  object PatternReplaceLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case PatternReplaceLensGoal(pattern, variables, after) =>
          in.exp match {
            case inExp@ADT(argsIn, adtBuilder) =>
              pattern match { // TODO: Pattern replace at higher level?
                case ADT(argsIn2, adtBuilder2) if isSameADT(inExp, pattern) =>
                  val argsMatched = argsIn.zip(argsIn2).map{
                    case (subIn, subPattern) =>
                      repair(
                        in.subExpr(subIn),
                        out.subExpr(
                          PatternMatchLensGoal(
                            subPattern, variables, false
                          )))
                  }
                  for{ argumentsCombined <-ContExp.regroupArguments(argsMatched)
                       (_, context) = argumentsCombined
                  } yield ContExp(after, context)

                case Var(v) =>
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

