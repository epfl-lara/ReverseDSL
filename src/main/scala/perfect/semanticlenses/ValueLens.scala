package perfect.semanticlenses

import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.{Log, ProgramFormula, semanticlenses}
import perfect.ReverseProgram.{Cache, maybeEvalWithCache, repair}
import perfect.Utils.isValue

/**
  * Created by Mikael on 05/05/2017.
  * Returns the original program if the value is unchanged
  */
object ValueLens extends SemanticLens {
  override def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    if(!out.expr.isInstanceOf[Variable] && in.getFunctionValue == Some(out.expr)) return {
      Log("@return original function");
      Stream(in.assignmentsAsOriginals() combineWith out.formula)
    } else {
      Stream.empty
    }
  }
  isPreemptive = true
}
