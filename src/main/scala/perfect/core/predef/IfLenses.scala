package perfect.core
package predef

trait IfLenses extends IfLensesLike { self: ProgramUpdater with ContExps with Lenses =>
  def extractIf(e: Exp): Option[(Exp, Exp, Exp)]
  def buildIf(cond: Exp, thn: Exp, elz: Exp): Exp

  object IfExtractor extends IfExprExtractor {
    def unapply(e: Exp) = extractIf(e)
    def apply(cond: Exp, thn: Exp, elz: Exp) = buildIf(cond, thn, elz)
  }

  object IfLens extends IfLensLike(IfExtractor)
}


