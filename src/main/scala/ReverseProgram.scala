import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import inox.InoxProgram

/**
  * Created by Mikael on 03/03/2017.
  */
object ReverseProgram {
  type FunctionEntry = Identifier
  type ModificationSteps = Unit
  type OutExpr = Expr
  import Utils._
  import Constrainable._
  lazy val context = Context.empty.copy(options = Options(Seq(optSelectedSolvers(Set("smt-cvc4")))))

  /** Reverses a parameterless function, if possible.*/
  def put[A: Constrainable](out: A, prevOut: Option[OutExpr], modif: Option[ModificationSteps], prevIn: Option[(InoxProgram, FunctionEntry)]): Iterable[(InoxProgram, FunctionEntry)] = {
    if(prevIn == None) {
      implicit val symbols = defaultSymbols
      val outExpr = inoxExprOf[A](out)
      val main = FreshIdentifier("main")
      val fundef = mkFunDef(main)()(stp => (Seq(), outExpr.getType, _ => outExpr))
      return Stream((InoxProgram(context, Seq(fundef), allConstructors), main))
    }
    val (prevProgram, prevFunctionEntry) = prevIn.get
    ???
  }
}
