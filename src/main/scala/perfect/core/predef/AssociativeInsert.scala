package perfect.core.predef

/**
  * Created by Mikael on 05/05/2017.
  */
object AssociativeInsert extends Enumeration {
  type InsertDirection = Value
  val InsertToLeft, InsertToRight, InsertAutomatic = Value
  def unapply(s: String): Option[InsertDirection] =
    values.find(_.toString == s)
}