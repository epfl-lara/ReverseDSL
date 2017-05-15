package perfect.core
package predef

/**
  * Created by Mikael on 09/05/2017.
  */

trait PatternMatchLenses extends PatternMatchLensesLike {
  self: ProgramUpdater
    with ContExps with Lenses with StringLenses with StringConcatLenses with ADTLenses =>

  /** Pattern match the input program, inserting the variables if forClone is activated.
    * The pattern with the vars replaced by their inputs must always be the original program value.
    **/
  def extractPatternMatchGoal(e: Exp): Option[(Exp, List[(Var, Exp)], Boolean)]
  def buildPatternMatchGoal(pattern: Exp, vars: List[(Var, Exp)], forClone: Boolean): Exp

  object PatternMatchLensGoal extends PatternMatchLensGoalExtractor {
    def unapply(e: Exp): Option[(Exp, List[(Var, Exp)], Boolean)] = extractPatternMatchGoal(e: Exp)
    def apply(pattern: Exp, vars: List[(Var, Exp)], forClone: Boolean): Exp = buildPatternMatchGoal(pattern, vars, forClone)
  }

  object PatternMatchLens extends PatternMatchLensLike(StringLiteral, StringConcat, ADT, PatternMatchLensGoal)
}

