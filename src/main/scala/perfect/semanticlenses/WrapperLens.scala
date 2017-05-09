package perfect
package semanticlenses
import Utils.ifEmpty
import inox.trees.Symbols
import perfect.ReverseProgram.Cache

/**
  * Created by Mikael on 08/05/2017.
  */
case class WrapperLens(normal: SemanticLens, wrapping: SemanticLens) extends SemanticLens {
  def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    if (in.isWrappingLowPriority) {
      (normal interleave wrapping).put(in, out)
    } else {
      (wrapping interleave normal).put(in, out)
    }
  }
}
