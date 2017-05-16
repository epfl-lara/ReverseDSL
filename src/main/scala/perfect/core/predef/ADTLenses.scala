package perfect.core
package predef


/**
  * Created by Mikael on 10/05/2017.
  * Algebraic data type lenses.
  */
trait ADTLenses extends ADTLensesLike {
  self: ProgramUpdater with ContExps with Lenses =>
  /** Returns the arguments of the ADT and a builder for it. */
  def extractADT(e: Exp): Option[(Seq[Exp], Seq[Exp] => Exp)]

  /** Returns
    * - the ADT expr being extracted
    * - A way to rebuild it
    * - A set of variables for the arguments of a new ADT
    * - The index of the selector among the arguments */
  def extractADTSelector(e: Exp)(implicit symbols: Symbols): Option[(Exp, Exp => Exp, Seq[Var], Int)]

  /** Returns true if e and g are two instances of the same ADT type */
  def isSameADT(e: Exp, g: Exp): Boolean

  object ADT extends ADTExtractor {
    def unapply(e: Exp): Option[(Seq[Exp], (Seq[Exp]) => Exp)] = extractADT(e)

    def isSame(e: Exp, g: Exp): Boolean = isSameADT(e, g)
  }

  object ADTSelector extends ADTSelectorExtractor {
    def unapply(e: Exp): Option[(Exp, (Exp) => Exp, Seq[Var], Int)] = extractADTSelector(e)
  }

  object ADTLens extends ADTLensLike(ADT, ADTSelector)
}


