package perfect.core
package predef

import perfect.core.predef.AssociativeInsert.InsertDirection


/**
  * Created by Mikael on 09/05/2017.
  */

trait PasteVariableLenses extends PasteVariableLensesLike { self: ProgramUpdater with ContExps with Lenses with StringLenses with StringConcatLenses =>
  def extractPasteStringVarGoal(e: Exp): Option[(String, Var, String, String, AssociativeInsert.InsertDirection)]

  def buildPasteStringVarGoal(left: String, v: Var, v_value: String, right: String, direction: AssociativeInsert.InsertDirection): Exp

  object PasteVariableLensGoal extends PasteVariableLensGoalExtractor {
    def unapply(e: Exp): Option[(String, Var, String, String, InsertDirection)] = extractPasteStringVarGoal(e)
    def apply(left: String, v: Var, v_value: String, right: String, direction: AssociativeInsert.InsertDirection): Exp =
      buildPasteStringVarGoal(left, v, v_value, right, direction)
  }

  object PasteVariableLens extends PasteVariableLens(StringConcat, PasteVariableLensGoal)
}







