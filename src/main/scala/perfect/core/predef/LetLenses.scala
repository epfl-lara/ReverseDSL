package perfect.core.predef

import perfect.core.{ContExps, Lenses, ProgramUpdater}

/**
  * Created by Mikael on 11/05/2017.
  */
trait LetLenses extends LetLensesLike {  self: ProgramUpdater with ContExps with Lenses with ApplicationLenses with LambdaLenses =>
  def extractLet(e: Exp): Option[(Var, Exp, Exp)]
  def buildLet(v: Var, assigned: Exp, body: Exp): Exp
  object LetExtractor extends LetExtractor {
    def unapply(e: Exp): Option[(Var, Exp, Exp)] = extractLet(e)
    def apply(v: Var, assigned: Exp, body: Exp): Exp = buildLet(v, assigned, body)
  }
  object LetLens extends LetLensLike(ApplicationExtractor, LambdaExtractor, LetExtractor)
}


