package perfect
package semanticlenses

import inox.trees.Symbols
import perfect.ReverseProgram.Cache

/**
  * Created by Mikael on 04/05/2017.
  */
trait SemanticLens { self =>
  def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula]
  /** If set to true, when it returns a solution, it discards others */
  var isPreemptive: Boolean = false
  def andThen(other: SemanticLens) = CombinedLens(self, other)
  def interleave(other: SemanticLens) = InterleavedLens(self, other)
}