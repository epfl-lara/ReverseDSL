package perfect
package semanticlenses

import inox.trees.Symbols
import perfect.ProgramFormula
import perfect.ReverseProgram.Cache

/**
  * Created by Mikael on 05/05/2017.
  */
case class InterleavedLens(self: SemanticLens, other: SemanticLens) extends SemanticLens {
  def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    Utils.interleave { self.put(in, out) } {other.put(in, out) }
  }
}
