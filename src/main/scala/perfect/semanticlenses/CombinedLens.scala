package perfect
package semanticlenses
import Utils.ifEmpty
import inox.trees.Symbols
import perfect.ReverseProgram.Cache

/**
  * Created by Mikael on 04/05/2017.
  */
case class CombinedLens(self: SemanticLens, other: SemanticLens) extends SemanticLens {
  def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    if(self.isPreemptive) {
      ifEmpty(self.put(in, out))(other.put(in, out))
    } else {
      self.put(in, out) #::: other.put(in, out)
    }
  }
  isPreemptive = self.isPreemptive
}
