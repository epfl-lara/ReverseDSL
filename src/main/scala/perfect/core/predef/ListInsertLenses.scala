package perfect.core
package predef

/**
  * Created by Mikael on 09/05/2017.
  */
trait ListInsertLenses extends ListInsertLensesLike { self: ProgramUpdater with ContExps with Lenses with ADTLenses with ListLenses =>
  /** Returns the head, the tail and a way to build a list from a sequence of elements. */
  def extractListInsertGoal(e: Exp): Option[(List[Exp], List[Exp], List[Exp],
    (List[Exp], Option[Exp]) => Exp,
    (List[Exp], List[Exp], List[Exp]) => Exp)]

  def buildListInsertGoal(before: List[Exp], inserted: List[Exp], after: List[Exp], direction: AssociativeInsert.InsertDirection)(implicit symbols: Symbols): Exp

  object ListInsertLensGoal extends ListInsertLensGoalExtractor {
    def unapply(e: Exp): Option[(List[Exp], List[Exp], List[Exp], (List[Exp], Option[Exp]) => Exp, (List[Exp], List[Exp], List[Exp]) => Exp)] = extractListInsertGoal(e)
    def apply(before: List[Exp], inserted: List[Exp], after: List[Exp], direction: AssociativeInsert.InsertDirection)(implicit symbols: Symbols): Exp =
      buildListInsertGoal(before, inserted, after, direction)

  }

  object ListInsertLens extends ListInsertLensLike(ListInsertLensGoal, Cons, ListLiteral)
}



