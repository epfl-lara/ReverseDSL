package perfect.core.predef

import perfect.core.{ContExps, Lenses, ProgramUpdater}

/**
  * Created by Mikael on 05/05/2017.
  */

trait LambdaLenses extends LambdaLensesLike { self: ProgramUpdater with ContExps with Lenses =>
  def extractLambda(e: Exp): Option[(Seq[Var], Exp, Exp => Exp)]
  def buildLambda(v: Seq[Var], body: Exp): Exp

  object LambdaExtractor extends LambdaExtractor {
    def unapply(e: Exp): Option[(Seq[Var], Exp, Exp => Exp)] = extractLambda(e)
    def apply(v: Seq[Var], body: Exp): Exp = buildLambda(v, body)
  }

  object LambdaLens extends LambdaLensLike(LambdaExtractor)
}


