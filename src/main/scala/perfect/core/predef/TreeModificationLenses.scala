package perfect.core
package predef

/**
  * Created by Mikael on 09/05/2017.
  */
trait TreeModificationLenses extends TreeModificationLensesLike {  self: ProgramUpdater with
  ContExps with Lenses with ADTLenses with ListLenses with ListConcatLenses =>
  /** Returns a lambda, the modified subtree, and an index indicating where the next change should happen with the new subgoal */
  def extractTreeModificationGoal(e: Exp)(implicit symbols: Symbols):
  Option[(Exp, Int)]

  /** Returns a goal with the modified tree, and the index where the modification occurred..*/
  def buildTreeModificationGoal(original: Exp, modified: Exp, index: Int)(implicit symbols: Symbols): Exp

  object TreeModificationLensGoal extends TreeModificationLensGoalExtractor {
    def unapply(e: Exp)(implicit symbols: Symbols): Option[(Exp, Int)]= extractTreeModificationGoal(e)
    def apply(original: Exp, modified: Exp, index: Int)(implicit symbols: Symbols): Exp = buildTreeModificationGoal(original, modified, index)
  }

  object TreeModificationLens extends TreeModificationLensLike(
    TreeModificationLensGoal,
    ADT,
    ListLiteral,
    ListConcat)
}




