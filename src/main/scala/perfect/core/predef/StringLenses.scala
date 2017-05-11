package perfect.core
package predef

/**
  * Created by Mikael on 10/05/2017.
  */
trait StringLenses { self: ProgramUpdater =>
  def extractStringliteral(e: Exp): Option[String]
  def buildStringLiteral(e: String): Exp

  object StringLiteral {
    def unapply(e: Exp) = extractStringliteral(e)
    def apply(e: String) = buildStringLiteral(e)
  }

  @inline def charType(a: Char): Int =
    if(a.isUpper) 1 else if(a.isLower) 2 else if(a.isSpaceChar) 5 else if(a == '\n' || a == '\r') 10 else 4 // 4 for punctuation.

  @inline def differentCharType(a: Char, b: Char): Int = {
    Math.abs(charType(a) - charType(b))
  }

  @inline def typeJump(a: String, b: String): Int = {
    if(a.nonEmpty && b.nonEmpty)
      differentCharType(a(a.length - 1), b(0))
    else 0 // We mostly insert into empty strings if available.
  }
}
