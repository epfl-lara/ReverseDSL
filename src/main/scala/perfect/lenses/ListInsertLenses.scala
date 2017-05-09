package perfect.lenses

import inox.trees
import perfect.InoxProgramUpdater


import inox.{FreshIdentifier, Identifier}
import perfect.InoxProgramUpdater
import perfect.semanticlenses.TreeWrap
import inox.trees._
import inox._
import inox.trees.dsl._

/**
  * Created by Mikael on 09/05/2017.
  */
trait ListInsertLenses { self: InoxProgramUpdater.type =>
  object ListInsertLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case ListInsertGoal(tpe, before, inserted, after) =>
          in.exp match {
            case ADT(adtType@ADTType(tp, tpArgs), argsIn) =>
              //Log("ListInsert")
              if(before.length == 0) { // Insertion happens before this element
                //Log("beforeLength == 0")
                // We might delete the elements afterwards.
                if(after.length == 0) {
                  //Log("afterLength == 0")
                  Stream(
                    out.subExpr(perfect.ListLiteral(inserted, tpe))
                  )
                } else { // after.length > 0
                  //Log("afterLength > 0")
                  in.getFunctionValue match {
                    case Some(ListLiteral(functionValueList, listBuilder)) =>
                      val newTail = listBuilder(functionValueList.tail)

                      if(after.length == functionValueList.length) { // No deletion.
                        //Log("afterLength == functionValueList.length")
                        for{ pf <- repair(in.subExpr(argsIn(0)).withComputedValue(functionValueList.head), out.subExpr(after.head))
                             pf2 <- repair(in.subExpr(argsIn(1)).withComputedValue(newTail),
                               out.subExpr(ListInsertGoal(tpe, Nil, Nil, after.tail))) } yield {
                          ContExp(perfect.ListLiteral.concat(
                            perfect.ListLiteral(inserted, tpe),
                            perfect.ListLiteral(List(pf.exp), tpe),
                            pf2.exp), pf.context combineWith pf2.context combineWith out.context)
                        }
                      } else {
                        //Log("afterLength < functionValueList.length")
                        assert(after.length < functionValueList.length) // some deletion happened.
                        val updatedOutProgram = out.subExpr(ListInsertGoal(tpe, Nil, Nil, after)) // Recursive problem if
                        for{ pf <- repair(in.subExpr(argsIn(1)).withComputedValue(newTail), updatedOutProgram)} yield {
                          pf.wrap{ x =>
                            perfect.ListLiteral.concat(
                              perfect.ListLiteral(inserted, tpe),
                              x
                            )
                          }
                        }
                      }

                    case _ => Stream.empty
                  }
                }
              } else { // before.length > 0
                assert(argsIn.length == 2, "supposed that there was an element here, but there was none.")
                val updatedOutProgram = out.subExpr(ListInsertGoal(tpe, before.tail, inserted, after))

                for{pfHead <- repair(in.subExpr(argsIn(0)), out.subExpr(before.head))
                    pfTail <- repair(in.subExpr(argsIn(1)), updatedOutProgram)} yield {
                  ContExp(perfect.ListLiteral.concat(perfect.ListLiteral(List(pfHead.exp), tpe), pfTail.exp),
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

object ListInsertGoal extends FunDefGoal {
  private val InsertList = FreshIdentifier("insertList")

  def apply(tpe: Type, leftUnmodified: List[Expr], inserted: List[Expr], rightUnmodified: List[Expr]): Expr = {
    E(InsertList)(tpe)(
      perfect.ListLiteral(leftUnmodified, tpe),
      perfect.ListLiteral(inserted, tpe),
      perfect.ListLiteral(rightUnmodified, tpe),
      StringLiteral(".") // Not used direction
    )
  }

  def unapply(e: Expr): Option[(Type, List[Expr], List[Expr], List[Expr])] = {
    e match {
      case FunctionInvocation(InsertList, Seq(tpe0), Seq(
      perfect.ListLiteral(leftBefore, _),
      perfect.ListLiteral(inserted, tpe3),
      perfect.ListLiteral(rightBefore, _),
      _)) =>
        Some((tpe0, leftBefore, inserted, rightBefore))
      case _ => None
    }
  }
  import perfect.Utils

  def funDef = mkFunDef(InsertList)("A"){ case Seq(tA) =>
    (Seq("left"::T(Utils.list)(tA), "inserted"::T(Utils.list)(tA), "right"::T(Utils.list)(tA), "direction"::StringType),
      T(Utils.list)(tA), {
      case Seq(left, inserted, right, direction) =>
        E(Utils.listconcat)(tA)(E(Utils.listconcat)(tA)(
          left,
          inserted),
          right)
    })
  }
}