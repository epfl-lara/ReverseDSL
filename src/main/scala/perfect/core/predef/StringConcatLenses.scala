package perfect.core.predef

import perfect.core._

/**
  * Created by Mikael on 09/05/2017.
  */

trait StringConcatLenses extends StringConcatLensesLike {
  self: ProgramUpdater with ContExps with Lenses with StringLenses =>
  def extractStringConcat(e: Exp): Option[(Exp, Exp)]
  def buildStringConcat(left: Exp, right: Exp): Exp
  def buildStringConcatSimplified(left: Exp, right: Exp): Exp
  def mkStringVar(name: String, avoid: Var*): Var

  object StringConcat extends StringConcatExtractor {
    def unapply(e: Exp): Option[(Exp, Exp)] = extractStringConcat(e)
    def apply(left: Exp, right: Exp): Exp = buildStringConcat(left, right)
    def apply(): Exp = StringLiteral("")
    def simplified(left: Exp, right: Exp): Exp = buildStringConcatSimplified(left, right)
  }

  object MkStringVar extends MkStringVar {
    def apply(name: String, avoid: Var*): Var = mkStringVar(name, avoid: _*)
  }

  object StringConcatLens extends StringConcatLensLike(StringLiteral, StringConcat, MkStringVar)
}


