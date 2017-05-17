package perfect.core
package predef

/**
  * Created by Mikael on 17/05/2017.
  */
trait ListConcatLenses extends ListConcatLensesLike { self: ProgramUpdater with ContExps with Lenses with ListLenses with ListLensesLike  =>
  /** Extracts the concatenation of two expressions computing lists */
  def extractListConcat(e: Exp): Option[(Exp, Exp, (Exp, Exp) => Exp)]

  /** Builds the concatenation of two expressions computing lists. */
  def buildListConcat(left: Exp, right: Exp)(implicit symbols: Symbols): Exp

  object ListConcat extends ListConcatExtractor {
    def unapply(e: Exp): Option[(Exp, Exp, (Exp, Exp) => Exp)] = extractListConcat(e)
    def apply(left: Exp, right: Exp)(implicit symbols: Symbols): Exp = buildListConcat(left, right)
  }

  object ListConcatLens extends ListConcatLensLike(ListLiteral, ListConcat)
}


