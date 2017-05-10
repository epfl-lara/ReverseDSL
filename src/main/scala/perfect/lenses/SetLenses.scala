package perfect.lenses
import perfect.core._
import perfect.core.predef._
import inox.trees.{FiniteSet, SetAdd}
import perfect.InoxProgramUpdater

/**
  * Created by Mikael on 10/05/2017.
  */
trait SetLenses { self: InoxProgramUpdater.type =>
  object SetLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      in.exp match {
        case l: FiniteSet =>
          lazy val evaledElements = l.elements.map{ e =>
            (in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(e))).getOrElse(return Stream.empty), e)
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

              case newOut => // Maybe it has a context ?
                Stream(out)
            }
          }
        case SetAdd(sExpr, elem) =>
          val sExpr_v = in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(sExpr))).getOrElse(return Stream.empty)
          val elem_v = in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(elem))).getOrElse(return Stream.empty)
          val FiniteSet(vs, tpe) = sExpr_v
          val FiniteSet(vsNew, _) = out.simplifiedExpr
          val vsSet = vs.toSet
          val vsNewSet = vsNew.toSet
          val maybeAddedElements = vsNewSet -- vsSet
          val maybeRemovedElements = vsSet -- vsNewSet
          val (changedElements, added, removed) = if(maybeAddedElements.size == 1 && maybeRemovedElements.size == 1) {
            (maybeRemovedElements.headOption.zip(maybeAddedElements.headOption).headOption: Option[(Exp, Exp)], Set[Exp](), Set[Exp]())
          } else
            (None: Option[(Exp, Exp)], maybeAddedElements: Set[Exp], maybeRemovedElements: Set[Exp])
          //Log(s"Added $added, Removed $removed, changed: $changedElements")
          changedElements match {
            case Some((old, fresh)) =>
              (if(vsSet contains old) {
                //Log.prefix("#1") :=
                  (for(pf <- repair(in.subExpr(sExpr),
                    out.subExpr(FiniteSet((vsSet - old + fresh).toSeq, tpe)))) yield {
                    pf.wrap(x => SetAdd(x, elem))
                  })
              } else Stream.empty) #::: (
                //Log.prefix("#2") :=
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
                     pfElem <- repair(in.subExpr(elem), ContExp(elem_v))
                } yield {
                  pf.wrap(x => SetAdd(x, pfElem.exp)) combineWith pfElem.context
                }
              } else {
                if(removed contains elem_v) { // We replace SetAdd(f, v) by f
                  for(pf <- repair(in.subExpr(sExpr),
                    out.subExpr(FiniteSet(vsSet.toSeq, tpe))
                  )) yield pf
                } else { // All changes happened in the single set.
                  for{pf <- repair(in.subExpr(sExpr),
                    out.subExpr(FiniteSet((vsSet ++ (added-elem_v) -- removed).toSeq, tpe)))
                      pfElem <- repair(in.subExpr(elem), ContExp(elem_v))
                  } yield pf.wrap(x => SetAdd(x, pfElem.exp)) combineWith pfElem.context
                }
              }
          }
        case _ => Stream.empty
      }
    }

    isPreemptive = true
  }
}
