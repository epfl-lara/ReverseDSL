package perfect
package semanticlenses

import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.ProgramFormula.CustomProgramFormula
import perfect.ReverseProgram.{Cache, maybeEvalWithCache, regroupArguments, repair}
import perfect.StringConcatExtended._


/**
  * Created by Mikael on 05/05/2017.
  */
object AssociativeInsert extends Enumeration {
  type InsertDirection = Value
  val InsertToLeft, InsertToRight, InsertAutomatic = Value
  def unapply(s: String): Option[InsertDirection] =
    values.find(_.toString == s)
}