package perfect.semanticlenses

/**
  * Created by Mikael on 09/05/2017.
  */

/** A FunDefGoal is a goal which can be build and unbuilt, to provide (out) semantics on how to repair the program */
trait FunDefGoal {
  import inox.trees.FunDef

  def funDef: FunDef
  def id = funDef.id
}
