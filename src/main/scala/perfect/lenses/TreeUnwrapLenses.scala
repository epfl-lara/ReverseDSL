package perfect.lenses

import perfect.core._
import perfect.core.predef._

/**
  * Created by Mikael on 09/05/2017.
  */
trait TreeUnwrapLenses { self: ProgramUpdater with ContExps with Lenses with ADTLenses =>

  /** Returns the original tree, and if needed to find a deeper subtree, return the index of the argument,
    * and the new goal based on the sub-tree of the original */
  def extractTreeUnwrapGoal(e: Exp)(implicit symbols: Symbols): Option[(Exp, Option[(Int, Exp)])]

  object TreeUnwrapLensGoal {
    def unapply(e: Exp)(implicit symbols: Symbols) = extractTreeUnwrapGoal(e)
  }

  object TreeUnwrapLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case TreeUnwrapLensGoal(original, subgoal) =>
          subgoal match {
            case None => Stream(in.assignmentsAsOriginals())
            case Some((index, treeUnwrapGoal)) =>
              in.exp match {
                case l@ADT(args, adtBuilder) =>
                  repair(in.subExpr(args(index)), out.subExpr(treeUnwrapGoal))
                case _ => Stream.empty
              }
          }
        case _ => Stream.empty
      }
    }
    isPreemptive = true
  }
}

