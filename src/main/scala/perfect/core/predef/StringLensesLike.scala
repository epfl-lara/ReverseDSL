package perfect.core
package predef

/**
  * Created by Mikael on 15/05/2017.
  */
trait StringLensesLike { self: ProgramUpdater =>
  trait StringLiteralExtractor {
    def unapply(e: Exp): Option[String]
    def apply(e: String): Exp

    def mkVar(name: String, avoid: Var*): Var = varFromExp(name, apply(""), false)
    def mkVar(original: Var, avoid: Var*): Var = freshen(original, avoid: _*)
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
