package perfect
package lenses
import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.ReverseProgram.{Cache, evalWithCache}
import perfect.Utils.isValue

/**
  * Created by Mikael on 05/05/2017.
  */
object SetLens extends semanticlenses.SemanticLens {
  def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    in.expr match {
      case l: FiniteSet =>
        lazy val evaledElements = l.elements.map{ e =>
          (evalWithCache(in.formula.assignments.get(e)), e)
        }
        def insertElementsIfNeeded(fs: FiniteSet) = {
          val expectedElements = fs.elements.toSet
          val newElements = evaledElements.filter{
            case (v, e) => expectedElements contains v
          }.map(_._2) ++ expectedElements.filter(x =>
            !evaledElements.exists(_._1 == x))
          Stream(out.subExpr(FiniteSet(newElements, fs.base)))
        }

        if(isValue(l) && out.simplifiedExpr.isInstanceOf[FiniteSet]) { // We should keep the same order if possible.
          out.simplifiedExpr match {
            case fs: FiniteSet => insertElementsIfNeeded(fs)
            case _ => Stream(out)
          }
        } else {
          out.simplifiedExpr match {
            case fs: FiniteSet =>
              // Since there is no order, there is no point repairing expressions,
              // only adding new ones and deleting old ones.
              insertElementsIfNeeded(fs)

            case newOut => // Maybe it has a formula ?
              Stream(out)
          }
        }
      case _ => Stream.empty
    }
  }

  isPreemptive = true
}
