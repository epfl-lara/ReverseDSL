package perfect.core
package predef

/**
  * Created by Mikael on 09/05/2017.
  */
trait InvocationLenses extends InvocationLensesLike {
  self: ProgramUpdater with ContExps with Lenses =>

  def extractInvocation(e: Exp)(implicit cache: Cache, symbols: Symbols):
  Option[(Seq[Exp], Seq[Exp] => Exp)]

  object InvocationExtractor extends InvocationExtractor {
    def unapply(e: Exp)(implicit cache: Cache, symbols: Symbols): Option[(Seq[Exp], (Seq[Exp]) => Exp)] =
      extractInvocation(e)
  }

  abstract class InvocationLens extends InvocationLensLike(InvocationExtractor)
}



