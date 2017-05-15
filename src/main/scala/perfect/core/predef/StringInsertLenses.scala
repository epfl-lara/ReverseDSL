package perfect.core.predef

import perfect.core._
import perfect.core.predef.AssociativeInsert.InsertDirection

/**
  * Created by Mikael on 09/05/2017.
  */


trait StringInsertLenses extends StringInsertLensesLike {
  self: ProgramUpdater with ContExps with Lenses with StringLenses with StringConcatLenses with AssociativeLenses =>
  def extractStringInsertGoal(e: Exp): Option[(String, String, String, AssociativeInsert.InsertDirection)]

  def buildStringInsertGoal(left: String, inserted: String, right: String, direction: AssociativeInsert.InsertDirection):
  Exp

  object StringInsertLensGoal extends StringInsertLensGoalExtractor {
    def unapply(e: Exp): Option[(String, String, String, InsertDirection)] = extractStringInsertGoal(e)

    def apply(left: String, inserted: String, right: String, direction: AssociativeInsert.InsertDirection): Exp =
      buildStringInsertGoal(left, inserted, right, direction)
  }

  object StringInsertLens extends StringInsertLensLike(StringLiteral, StringConcat, StringInsertLensGoal)

}



