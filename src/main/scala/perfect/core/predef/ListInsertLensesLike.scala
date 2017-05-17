package perfect.core
package predef

/**
  * Created by Mikael on 15/05/2017.
  */
trait ListInsertLensesLike { self: ProgramUpdater with ContExps with Lenses with ADTLenses with ListLensesLike =>
  trait ListInsertLensGoalExtractor {
    def unapply(e: Exp): Option[(List[Exp], List[Exp], List[Exp],
      (List[Exp], Option[Exp]) => Exp,
      (List[Exp], List[Exp], List[Exp]) => Exp)]
    def apply(before: List[Exp], inserted: List[Exp], after: List[Exp], direction: AssociativeInsert.InsertDirection)(implicit symbols: Symbols): Exp
    def apply(before: List[Exp], inserted: List[Exp], after: List[Exp])(implicit symbols: Symbols): Exp =
      apply(before, inserted, after, AssociativeInsert.InsertAutomatic)
  }

  class ListInsertLensLike(ListInsertLensGoal: ListInsertLensGoalExtractor, Cons: ListConsExtractor, ListLiteral: ListLiteralExtractor) extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case ListInsertLensGoal(before, inserted, after, listBuilder, listInsertGoalBuilder) =>
          in.exp match {
            case ListLiteral(Nil, literalListBuilder) =>
              Stream(ContExp(literalListBuilder(before ++ inserted ++ after), out.context))
            case Cons(head, tail, literalListBuilder) =>
              //perfect.Log("ListInsert")
              if(before.isEmpty) { //Log("beforeLength == 0")  // Insertion happens before this element
                if(after.isEmpty) { //Log("afterLength == 0")// We might delete the elements afterwards.
                  Stream(out.subExpr(listBuilder(inserted, None)))
                } else { // after.length > 0
                  //perfect.Log("afterLength > 0")
                  in.getFunctionValue match {
                    case Some(ListLiteral(functionValueList, _)) =>
                      val newTail = literalListBuilder(functionValueList.tail)

                      if(after.length == functionValueList.length) { // No deletion.
                        //perfect.Log("afterLength == functionValueList.length")
                        val repairedHead = repair(in.subExpr(head).withComputedValue(functionValueList.head), out.subExpr(after.head))
                        val repairedTail = if(after.tail.nonEmpty) {
                          repair(in.subExpr(tail).withComputedValue(newTail), out.subExpr(listBuilder(after.tail, None)))
                        } else {
                          Stream(ContExp(listBuilder(Nil, None)))
                        }

                        for{ pf <- repairedHead
                             pf2 <- repairedTail} yield {
                          ContExp(listBuilder(inserted :+ pf.exp, Some(pf2.exp)), pf.context combineWith pf2.context combineWith out.context)
                        }
                      } else {
                        //perfect.Log("afterLength < functionValueList.length")
                        assert(after.length < functionValueList.length) // some deletion happened.
                        val updatedOutProgram = out.subExpr(listInsertGoalBuilder(Nil, Nil, after)) // Recursive problem if
                        for{ pf <- repair(in.subExpr(tail).withComputedValue(newTail), updatedOutProgram)} yield {
                          pf.wrap{ x => listBuilder(inserted, Some(x)) }
                        }
                      }

                    case _ => Stream.empty
                  }
                }
              } else { // before.length > 0
                val updatedOutProgram = out.subExpr(listInsertGoalBuilder(before.tail, inserted, after))

                for{pfHead <- repair(in.subExpr(head), out.subExpr(before.head))
                    pfTail <- repair(in.subExpr(tail), updatedOutProgram)} yield {
                  ContExp(listBuilder(List(pfHead.exp), Some(pfTail.exp)),
                    pfHead.context combineWith pfTail.context
                  )
                }
              }

            case _ =>
              Stream.empty
          }
        case _ => Stream.empty
      }
    }
    isPreemptive = true
  }
}
