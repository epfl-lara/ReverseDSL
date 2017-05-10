package perfect
package semanticlenses
import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.ReverseProgram.{Cache, maybeEvalWithCache, repair}
import perfect.Utils.isValue

/**
  * Created by Mikael on 05/05/2017.
  */
object SetLens extends SemanticLens {
  def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    in.expr match {
      case l: FiniteSet =>
        lazy val evaledElements = l.elements.map{ e =>
          (maybeEvalWithCache(in.formula.assignments.get(e)).getOrElse(return Stream.empty), e)
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
      case SetAdd(sExpr, elem) =>
        val sExpr_v = in.formula.assignments.flatMap(assign => maybeEvalWithCache(assign(sExpr))).getOrElse(return Stream.empty)
        val elem_v = in.formula.assignments.flatMap(assign => maybeEvalWithCache(assign(elem))).getOrElse(return Stream.empty)
        val FiniteSet(vs, tpe) = sExpr_v
        val FiniteSet(vsNew, _) = out.simplifiedExpr
        val vsSet = vs.toSet
        val vsNewSet = vsNew.toSet
        val maybeAddedElements = vsNewSet -- vsSet
        val maybeRemovedElements = vsSet -- vsNewSet
        val (changedElements, added, removed) = if(maybeAddedElements.size == 1 && maybeRemovedElements.size == 1) {
          (maybeRemovedElements.headOption.zip(maybeAddedElements.headOption).headOption: Option[(Expr, Expr)], Set[Expr](), Set[Expr]())
        } else
          (None: Option[(Expr, Expr)], maybeAddedElements: Set[Expr], maybeRemovedElements: Set[Expr])
        Log(s"Added $added, Removed $removed, changed: $changedElements")
        changedElements match {
          case Some((old, fresh)) =>
            (if(vsSet contains old) {
              Log.prefix("#1") :=
                (for(pf <- repair(in.subExpr(sExpr),
                  out.subExpr(FiniteSet((vsSet - old + fresh).toSeq, tpe)))) yield {
                  pf.wrap(x => SetAdd(x, elem))
                })
            } else Stream.empty) #::: (
              Log.prefix("#2") :=
                (if(elem_v == old) {
                  for(pf <- repair(in.subExpr(elem), out.subExpr(fresh))) yield {
                    pf.wrap(x => SetAdd(sExpr, x))
                  }
                } else Stream.empty)
              )
          case None => // Just added and removed elements.
            if(removed.isEmpty) { // Just added elements.
              for {pf <- repair(in.subExpr(sExpr),
                out.subExpr(FiniteSet((vsSet ++ (added - elem_v)).toSeq, tpe)))
                   pfElem <- repair(in.subExpr(elem), ProgramFormula(elem_v))
              } yield {
                pf.wrap(x => SetAdd(x, pfElem.expr)) combineWith pfElem.formula
              }
            } else {
              if(removed contains elem_v) { // We replace SetAdd(f, v) by f
                for(pf <- repair(in.subExpr(sExpr),
                  out.subExpr(FiniteSet(vsSet.toSeq, tpe))
                )) yield pf
              } else { // All changes happened in the single set.
                for{pf <- repair(in.subExpr(sExpr),
                  out.subExpr(FiniteSet((vsSet ++ (added-elem_v) -- removed).toSeq, tpe)))
                    pfElem <- repair(in.subExpr(elem), ProgramFormula(elem_v))
                } yield pf.wrap(x => SetAdd(x, pfElem.expr)) combineWith pfElem.formula
              }
            }
        }
      case _ => Stream.empty
    }
  }

  isPreemptive = true
}
