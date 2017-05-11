package perfect.semanticlenses

import perfect.lenses.FunDefGoal
import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.StringConcatExtended._

/**
  * Created by Mikael on 11/05/2017.
  */
object StringInsertGoal extends FunDefGoal {
  private val InsertString = FreshIdentifier("insertString")
  import perfect.core.predef.AssociativeInsert
  import AssociativeInsert._

  def apply(left: String, s: String, right: String, direction: InsertDirection): Expr = {
    E(InsertString)(StringLiteral(left), StringLiteral(s), StringLiteral(right), StringLiteral(direction.toString))
  }

  def unapply(e: Expr): Option[(String, String, String, InsertDirection)] = {
    e match {
      case FunctionInvocation(InsertString, Seq(), Seq(
      StringLiteral(leftBefore), StringLiteral(inserted), StringLiteral(rightBefore), StringLiteral(AssociativeInsert(direction))
      )) =>
        Some((leftBefore, inserted, rightBefore, direction))
      case _ =>
        None
    }
  }

  def funDef = mkFunDef(InsertString)(){ case _ =>
    (Seq("left"::StringType, "inserted"::StringType, "right"::StringType, "direction"::StringType),
      StringType,
      {
        case Seq(left, inserted, right, direction) =>
          left +& inserted +& right // Dummy
      })
  }
}
