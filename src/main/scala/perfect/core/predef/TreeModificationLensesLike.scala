package perfect.core
package predef

/**
  * Created by Mikael on 18/05/2017.
  */
trait TreeModificationLensesLike {  self: ProgramUpdater with
  ContExps with Lenses with ADTLensesLike with ListLenses with ListConcatLensesLike=>

  trait TreeModificationLensGoalExtractor { Self =>
    def unapply(e: Exp)(implicit symbols: Symbols): Option[(Exp, Int)]
    def apply(original: Exp, modified: Exp, index: Int)(implicit symbols: Symbols): Exp

    def apply(original: Exp, selector: (Exp, Int) => Exp, modified: Exp, indices: List[Int])(implicit symbols: Symbols): Exp =
      indices match {
        case Nil => modified
        case head::tail =>
          Self(original, Self(selector(original, head), selector, modified, tail), head)
      }

    /** For ADT-based lists only, recovers the sub-goal for target element and its index. */
    def indexOfElemModifiedInList(goal: Exp, index: Int = 0): Option[(Exp, Int)] = {
      goal match {
        case Self(subgoal, 1) =>
          indexOfElemModifiedInList(subgoal, index + 1)
        case Self(subgoal, 0) =>
          Some((goal, index))
        case _ =>
          None
      }
    }
  }

  class TreeModificationLensLike(
      TreeModificationLensGoal: TreeModificationLensGoalExtractor,
      ADT: ADTExtractor,
      ListLiteral: ListLiteralExtractor,
      ListConcat: ListConcatExtractor) extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case tm@TreeModificationLensGoal(modified, index) =>
          in.exp match {
            case l@ADT(args, adtBuilder) =>
              for {pf <- repair(in.subExpr(args(index)),
                out.subExpr(modified))} yield {
                pf.wrap(x => adtBuilder(args.take(index) ++ List(x) ++ args.drop(index + 1)))
              }
            case ListConcat(left, right, listConcatBuilder) =>
              val (subgoal, n) = TreeModificationLensGoal.indexOfElemModifiedInList(tm).getOrElse(return Stream.empty)
              val leftValue = in.maybeEval(left).getOrElse(return Stream.empty)
              leftValue match {
                case ListLiteral(l, lBuilder) =>
                  if(n < l.length) {
                    for(pf <- repair(in.subExpr(left), out.subExpr(subgoal))) yield {
                      pf.wrap(listConcatBuilder(_, right))
                    }
                  } else {
                    for(pf <- repair(in.subExpr(right), out.subExpr(subgoal))) yield {
                      pf.wrap(listConcatBuilder(left, _))
                    }
                  }
                case _ => Stream.empty
              }
            case _ => Stream.empty
          }
        case _ => Stream.empty
      }
    }
  }
}
