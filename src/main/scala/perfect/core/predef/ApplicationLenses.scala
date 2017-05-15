package perfect.core
package predef

/**
  * Created by Mikael on 10/05/2017.
  */

/** Default helper to create application extractions. for more advanced usages, see [[ApplicationLensesLike]] */
trait ApplicationLenses extends ApplicationLensesLike with LambdaLenses { self: ProgramUpdater with ContExps with Lenses with LambdaLenses =>
  def buildApplication(lambda: Exp, args: Seq[Exp]): Exp
  def extractApplication(e: Exp): Option[(Exp, Seq[Exp])]

  object ApplicationExtractor extends ApplicationExtractor {
    def apply(lambda: Exp, args: Seq[Exp]): Exp = buildApplication(lambda, args)
    def unapply(e: Exp): Option[(Exp, Seq[Exp])] = extractApplication(e)
  }
  object ApplicationLens extends ApplicationLensLike(ApplicationExtractor, LambdaExtractor)
}


