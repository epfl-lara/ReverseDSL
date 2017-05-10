package perfect.core.predef

import perfect.core._

/**
  * Created by Mikael on 10/05/2017.
  */
trait SetLenses { self: ProgramUpdater with ContExps with Lenses =>
  /** Returns the elements defining the set, and a way to build it back. */
  def extractSet(e: Exp): Option[(Seq[Exp], Seq[Exp] => Exp)]

  /** Returns the set and the added element */
  def extractSetAdd(e: Exp): Option[(Exp, Exp)]
  def buildSetAdd(set: Exp, elem: Exp): Exp

  private object FiniteSet {
    def unapply(e: Exp) = extractSet(e)
  }

  private object FiniteSetAdd {
    def unapply(e: Exp) = extractSetAdd(e)
    def apply(set: Exp, elem: Exp) = buildSetAdd(set, elem)
  }

  object SetLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      in.exp match {
        case l@FiniteSet(elements, builder) =>
          lazy val evaledElements = elements.map{ e =>
            (in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(e))).getOrElse(return Stream.empty), e)
          }
          def insertElementsIfNeeded(fsElements: Seq[Exp], fsBuilder: Seq[Exp] => Exp) = {
            val expectedElements = fsElements.toSet
            val newElements = evaledElements.filter{
              case (v, e) => expectedElements contains v
            }.map(_._2) ++ expectedElements.filter(x =>
              !evaledElements.exists(_._1 == x))
            Stream(out.subExpr(fsBuilder(newElements)))
          }

          out.simplifiedExpr match { // Todo: Repair if exactly one addition, one deletion ?
            case outFs@FiniteSet(outElements, outBuilder) =>
                // Since there is no order, there is no point repairing expressions,
                // only adding new ones and deleting old ones.
                insertElementsIfNeeded(outElements, outBuilder)

            case newOut => // Maybe it has a context ?
              Stream(out)
          }
        case FiniteSetAdd(sExpr, elem) =>
          val sExpr_v = in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(sExpr))).getOrElse(return Stream.empty)
          val elem_v = in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(elem))).getOrElse(return Stream.empty)
          val (vs, builder) = sExpr_v match {
            case FiniteSet(vs, builder) => (vs, builder)
            case _ => return Stream.empty
          }
          val (vsNew, _) = out.simplifiedExpr match {
            case FiniteSet(vsNew, builderNew) => (vsNew, builderNew)
            case _ => return Stream.empty
          }
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
                    out.subExpr(builder((vsSet - old + fresh).toSeq)))) yield {
                    pf.wrap(x => FiniteSetAdd(x, elem))
                  })
              } else Stream.empty) #::: (
                //Log.prefix("#2") :=
                  (if(elem_v == old) {
                    for(pf <- repair(in.subExpr(elem), out.subExpr(fresh))) yield {
                      pf.wrap(x => FiniteSetAdd(sExpr, x))
                    }
                  } else Stream.empty)
                )
            case None => // Just added and removed elements.
              if(removed.isEmpty) { // Just added elements.
                for {pf <- repair(in.subExpr(sExpr),
                  out.subExpr(builder((vsSet ++ (added - elem_v)).toSeq)))
                     pfElem <- repair(in.subExpr(elem), ContExp(elem_v))
                } yield {
                  pf.wrap(x => FiniteSetAdd(x, pfElem.exp)) combineWith pfElem.context
                }
              } else {
                if(removed contains elem_v) { // We replace SetAdd(f, v) by f
                  for(pf <- repair(in.subExpr(sExpr),
                    out.subExpr(builder(vsSet.toSeq))
                  )) yield pf
                } else { // All changes happened in the single set.
                  for{pf <- repair(in.subExpr(sExpr),
                    out.subExpr(builder((vsSet ++ (added-elem_v) -- removed).toSeq)))
                      pfElem <- repair(in.subExpr(elem), ContExp(elem_v))
                  } yield pf.wrap(x => FiniteSetAdd(x, pfElem.exp)) combineWith pfElem.context
                }
              }
          }
        case _ => Stream.empty
      }
    }

    isPreemptive = true
  }
}
