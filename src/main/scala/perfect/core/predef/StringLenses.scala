package perfect.core
package predef

/**
  * Created by Mikael on 10/05/2017.
  */
trait StringLenses extends StringLensesLike {
  self: ProgramUpdater =>
  def extractStringliteral(e: Exp): Option[String]
  def buildStringLiteral(e: String): Exp

  object StringLiteral extends StringLiteralExtractor {
    def unapply(e: Exp): Option[String] = extractStringliteral(e)
    def apply(e: String): Exp = buildStringLiteral(e)
  }
}


