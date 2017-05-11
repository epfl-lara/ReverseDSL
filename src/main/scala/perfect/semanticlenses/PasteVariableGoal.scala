package perfect.semanticlenses

import perfect.core.predef.AssociativeInsert
import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.StringConcatExtended._

/**
  * Created by Mikael on 11/05/2017.
  */
object PasteVariableGoal extends FunDefGoal {
  private val Paste = FreshIdentifier("pastevariable")
  def apply(left: String, insertedVar: Variable, originalVarValue: String, right: String, direction: AssociativeInsert.InsertDirection): Expr = {
    E(Paste)(
      StringLiteral(left),
      insertedVar,
      StringLiteral(originalVarValue),
      StringLiteral(right),
      StringLiteral(direction.toString)
    )
  }

  def unapply(f: Expr): Option[(String, Variable, String, String, AssociativeInsert.InsertDirection)] = {
    f match {
      case FunctionInvocation(Paste, Seq(), Seq(
      StringLiteral(leftBefore),
      inserted: Variable,
      StringLiteral(insertedValue),
      StringLiteral(rightBefore),
      StringLiteral(AssociativeInsert(direction))
      )) =>
        Some((leftBefore, inserted, insertedValue, rightBefore, direction))
      case _ =>
        None
    }
  }

  def funDef = mkFunDef(Paste)(){ case _ =>
    (Seq("left"::StringType, "pasted"::StringType,  "originalvalue"::StringType, "right"::StringType, "direction"::StringType),
      StringType,
      {
        case Seq(left, pasted, originalvalue, right, direction) =>
          left +& originalvalue +& right // Dummy
      })
  }
}
