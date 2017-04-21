package perfect

import inox._

/**
  * Created by Mikael on 13/03/2017.
  */
trait LambdaPreservingEvaluator extends inox.evaluators.RecursiveEvaluator {
  self =>
  override val name = "Lambda-preserving recursive Evaluator"

  val program: Program
  import program._
  import program.trees._
  import program.symbols._
  import exprOps._

  override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case l@Lambda(_, _) =>
      val mapping = variablesOf(l).map(v => v -> rctx.mappings(v.toVal)).toMap
      replaceFromSymbols(mapping, l)
    case FunctionInvocation(Utils.stringCompare, Seq(), Seq(left, right)) =>
      val StringLiteral(s) = e(left)
      val StringLiteral(t) = e(right)
      if (s < t) {
        IntegerLiteral(-1)
      } else if (s == t) {
        IntegerLiteral(0)
      } else {
        IntegerLiteral(1)
      }
    case _ => super.e(expr)
  }
}
