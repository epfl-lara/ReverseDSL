package perfect.core
package predef

/**
  * Created by Mikael on 09/05/2017.
  */
trait InvocationLenses extends InvocationLensesLike {
  self: ProgramUpdater with ContExps with Lenses =>

  def extractInvocation(e: Exp)(implicit cache: Cache, symbols: Symbols):
  Option[(Seq[Exp], Seq[Exp] => Exp)]

  def isSameInvocation(e1: Exp, e2: Exp)(implicit cache: Cache, symbols: Symbols): Boolean

  object InvocationExtractor extends InvocationExtractor {
    def unapply(e: Exp)(implicit cache: Cache, symbols: Symbols): Option[(Seq[Exp], (Seq[Exp]) => Exp)] =
      extractInvocation(e)

    def isSame(e: Exp, f: Exp)(implicit cache: Cache, symbols: Symbols): Boolean = isSameInvocation(e, f)
  }

  abstract class InvocationLens extends InvocationLensLike(InvocationExtractor)
}



