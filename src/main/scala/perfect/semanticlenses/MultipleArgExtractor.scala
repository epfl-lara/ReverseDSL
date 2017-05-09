package perfect
package semanticlenses

import inox.trees._
import perfect.ReverseProgram.Cache

/**
  * Created by Mikael on 09/05/2017.
  */
trait MultipleArgExtractor {
  /** The first argument is the raw list of arguments
    * The second return element is a function which, given an evaluator from the expr to their values with in.formula, and out, returns a stream of arguments with a new fomrula.
    * The third return element is a function which recombines multiple arguments into a single expression. */
  def extract(e: Expr)(implicit cache: Cache, symbols: Symbols): Option[
    ( Seq[Expr],
      (Seq[ProgramFormula], ProgramFormula) => Stream[(Seq[ProgramFormula], Formula)],
      Seq[Expr] => Expr
      )]
}
