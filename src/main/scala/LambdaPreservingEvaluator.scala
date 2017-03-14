import inox.{Options, Program}

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
    case _ => super.e(expr)
  }
}