package perfect.core
package predef
import scala.collection.mutable.ListBuffer


/**
  * Created by Mikael on 10/05/2017.
  * Algebraic data type lenses.
  */
trait ADTLenses extends ADTLensesLike with ContExps {
  self: ProgramUpdater with Lenses =>
  /** Returns the arguments of the ADT and a builder for it. */
  def extractADT(e: Exp): Option[(Seq[Exp], Seq[Exp] => Exp)]

  /** Returns
    * - the ADT expr being extracted
    * - A way to rebuild it
    * - A set of variables for the arguments of a new ADT
    * - The index of the selector among the arguments */
  def extractADTSelector(e: Exp)(implicit symbols: Symbols): Option[(Exp, Exp => Exp, Seq[Var], Int)]

  /** Returns true if e and g are two instances of the same ADT type */
  def isSameADT(e: Exp, g: Exp): Boolean

  override def buildMergeCommands: ListBuffer[MergeCommand] = super.buildMergeCommands += ADT

  object ADT extends ADTExtractor with MergeCommand {
    def unapply(e: Exp): Option[(Seq[Exp], (Seq[Exp]) => Exp)] = extractADT(e)

    def isSame(e: Exp, g: Exp): Boolean = isSameADT(e, g)

    override def merge(e1: Exp, e2: Exp)(implicit symbols: Symbols): Option[(Exp, Seq[(Var, KnownValue)])] = {
      e2 match {
        case e2@ADT(vars1, v1Builder) if vars1.forall(isVar) =>
          e1 match {
            case ADT(vars2, v2Builder) if vars2.forall(isVar) && ADT.isSame(e1, e2) =>
              val vvars1 = vars1.collect[Var, Seq[Var]] { case Var(v) => v }
              val vvars2 = vars2.collect[Var, Seq[Var]] { case Var(v) => v }
              Some((e1, vars1.zip(vvars2).map{ case (Var(x1), x2) =>
                x1 -> StrongValue(x2)
              }))
            case _ => None
          }
        case _ => None
      }
    }
  }

  object ADTSelector extends ADTSelectorExtractor {
    def unapply(e: Exp): Option[(Exp, (Exp) => Exp, Seq[Var], Int)] = extractADTSelector(e)
  }

  object ADTLens extends ADTLensLike(ADT, ADTSelector)
}


