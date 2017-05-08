package perfect
package semanticlenses

import Utils.ifEmpty
import inox.trees.Symbols
import perfect.ReverseProgram.Cache

/**
  * Created by Mikael on 04/05/2017.
  */
case object NoChangeLens extends SemanticLens {
  isPreemptive = true
  def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    if(in.expr == out.expr) return {
      Stream(in.assignmentsAsOriginals()) /:: Log.prefix("@return original without constraints:")
    } else Stream.empty
  }
}
