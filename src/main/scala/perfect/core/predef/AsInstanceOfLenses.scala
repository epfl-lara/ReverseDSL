package perfect.core.predef

import perfect.core.{ContExps, Lenses, ProgramUpdater}

/**
  * Created by Mikael on 11/05/2017.
  */
trait AsInstanceOfLenses extends AsInstanceOfLensesLike { self: ProgramUpdater with ContExps with Lenses =>
  /** Returns the inner element and a wrapper around it. */
  def extractAsInstanceOf(e: Exp): Option[(Exp, Exp => Exp)]

  object AsInstanceOfExtractor extends AsInstanceOfExtractor {
    def unapply(e: Exp) = extractAsInstanceOf(e)
  }

  object AsInstanceOfLens extends AsInstanceOfLensLike(AsInstanceOfExtractor)
}


