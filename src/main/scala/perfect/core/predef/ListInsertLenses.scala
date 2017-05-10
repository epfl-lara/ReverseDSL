package perfect.core
package predef

/**
  * Created by Mikael on 09/05/2017.
  */
trait ListInsertLenses { self: ProgramUpdater with ContExps with Lenses with ADTLenses with ListLenses =>
  /** Returns the head, the tail and a way to build a list from a sequence of elements. */
  def extractListInsertGoal(e: Exp): Option[(List[Exp], List[Exp], List[Exp],
    (List[Exp], Option[Exp]) => Exp,
    (List[Exp], List[Exp], List[Exp]) => Exp)]

  object ListInsertLensGoal {
    def unapply(e: Exp) = extractListInsertGoal(e)
  }

  object ListInsertLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case ListInsertLensGoal(before, inserted, after, listBuilder, listInsertGoalBuilder) =>
          in.exp match {
            case Cons(head, tail, literalListBuilder) =>
              //Log("ListInsert")
              if(before.length == 0) { //Log("beforeLength == 0")  // Insertion happens before this element
                if(after.length == 0) { //Log("afterLength == 0")// We might delete the elements afterwards.
                  Stream(out.subExpr(listBuilder(inserted, None)))
                } else { // after.length > 0
                  //Log("afterLength > 0")
                  in.getFunctionValue match {
                    case Some(ListLiteral(functionValueList, _)) =>
                      val newTail = literalListBuilder(functionValueList.tail)

                      if(after.length == functionValueList.length) { // No deletion.
                        //Log("afterLength == functionValueList.length")
                        for{ pf <- repair(in.subExpr(head).withComputedValue(functionValueList.head), out.subExpr(after.head))
                             pf2 <- repair(in.subExpr(tail).withComputedValue(newTail),
                               out.subExpr(listInsertGoalBuilder(Nil, Nil, after.tail))) } yield {
                          ContExp(listBuilder(inserted :+ pf.exp, Some(pf2.exp)), pf.context combineWith pf2.context combineWith out.context)
                        }
                      } else {
                        //Log("afterLength < functionValueList.length")
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

