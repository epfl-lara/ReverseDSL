package perfect.core
package predef

/**
  * Created by Mikael on 10/05/2017.
  */
trait ApplicationLenses { self: ProgramUpdater =>
  def buildApplication(lambda: Exp, args: Seq[Exp]): Exp
  def extractApplication(e: Exp): Option[(Exp, Seq[Exp])]

  object Application {
    def apply(lambda: Exp, args: Seq[Exp]): Exp = buildApplication(lambda, args)
    def unapply(e: Exp) = extractApplication(e)
  }
}
