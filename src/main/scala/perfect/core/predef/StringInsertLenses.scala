package perfect.core.predef

import perfect.core._
import perfect.core.predef.AssociativeInsert.InsertDirection

import scala.collection.mutable.ListBuffer

/**
  * Created by Mikael on 09/05/2017.
  */


trait StringInsertLenses extends ContExps with StringInsertLensesLike{
  self: ProgramUpdater with Lenses with StringLenses with StringConcatLenses with AssociativeLenses =>
  def extractStringInsertGoal(e: Exp): Option[(String, String, String, AssociativeInsert.InsertDirection)]

  def buildStringInsertGoal(left: String, inserted: String, right: String, direction: AssociativeInsert.InsertDirection):
  Exp

  override def buildContExpCommands = super.buildContExpCommands += StringInsertLensGoal

  object StringInsertLensGoal extends StringInsertLensGoalExtractor with ContExpCommand  {
    def unapply(e: Exp): Option[(String, String, String, InsertDirection)] = extractStringInsertGoal(e)

    def apply(left: String, inserted: String, right: String, direction: AssociativeInsert.InsertDirection): Exp =
      buildStringInsertGoal(left, inserted, right, direction)

    object Eval extends EvalContExpCommand {
      def unapply(e: Exp): Option[Exp] = e match {
        case StringInsertLensGoal(left, middle, right, direction) => Some(StringLiteral(left + middle + right))
        case _ => None
      }
    }

    def merge(e1: Exp, e2: Exp)(implicit symbols: Symbols): Option[(Exp, Seq[(Var, KnownValue)])] = None
  }

  object StringInsertLens extends StringInsertLensLike(StringLiteral, StringConcat, StringInsertLensGoal)

}



