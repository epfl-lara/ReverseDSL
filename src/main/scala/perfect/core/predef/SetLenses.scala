package perfect.core
package predef

/**
  * Created by Mikael on 10/05/2017.
  */

trait SetLenses extends SetLensesLike {
  self: ProgramUpdater with ContExps with Lenses =>
  /** Returns the elements defining the set, and a way to build it back. */
  def extractSet(e: Exp): Option[(Seq[Exp], Seq[Exp] => Exp)]

  /** Returns the set and the added element */
  def extractSetAdd(e: Exp): Option[(Exp, Exp)]
  def buildSetAdd(set: Exp, elem: Exp): Exp

  private object FiniteSet extends FiniteSetExtractor{
    def unapply(e: Exp): Option[(Seq[Exp], (Seq[Exp]) => Exp)] = extractSet(e)
  }

  private object FiniteSetAdd extends FiniteSetAddExtractor {
    def unapply(e: Exp): Option[(Exp, Exp)] = extractSetAdd(e)
    def apply(set: Exp, elem: Exp): Exp = buildSetAdd(set, elem)
  }

  object SetLens extends SetLensLike(FiniteSet, FiniteSetAdd)
}


