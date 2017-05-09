package perfect
package renderer
import inox._
import inox.trees._

/**
  * Created by Mikael on 27/04/2017.
  */
object TipRenderer extends inox.ast.Printer {
  val trees = inox.trees
  implicit val symbols = {
    Utils.defaultSymbols.withFunctions(lenses.Lenses.funDefs)
  }
  lazy val context = Context.empty.copy(options = Options(Seq(optSelectedSolvers(Set("smt-cvc4")))))
  lazy val prog = InoxProgram(context, symbols)

  def printTip(e: Expr) = {
    val sc = new java.io.StringWriter()
    val tipPrinter = new inox.tip.Printer(prog, sc)
    tipPrinter.printScript(e)
    var res = sc.toString
    if(res.startsWith("(assert ")) {
      res = res.substring("(assert ".length, res.length - "(assert )".length)
    }
    res
  }

  override protected def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case e: Expr =>
      p"${printTip(e)}"
    case _ => super.ppBody(tree)
  }
}