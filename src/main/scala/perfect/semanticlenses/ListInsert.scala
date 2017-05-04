package perfect
package semanticlenses

import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.ProgramFormula.CustomProgramFormula
import perfect.ReverseProgram.{Cache, maybeEvalWithCache, regroupArguments, repair}
import perfect.StringConcatExtended._


/**
  * Created by Mikael on 04/05/2017.
  */
object ListInsert extends CustomProgramFormula  {
  object Lens extends SemanticLens {
    def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
      out.simplifiedExpr match {
        case ListInsert.Expr(tpe, before, inserted, after) =>
          in.expr match {
            case ADT(adtType@ADTType(tp, tpArgs), argsIn) =>
              Log("ListInsert")
              if(before.length == 0) { // Insertion happens before this element
                Log("beforeLength == 0")
                // We might delete the elements afterwards.
                if(after.length == 0) {
                  Log("afterLength == 0")
                  Stream(
                    ProgramFormula(ListLiteral(inserted, tpe), out.formula)
                  )
                } else { // after.length > 0
                  Log("afterLength > 0")
                  in.getFunctionValue match {
                    case Some(ListLiteral(functionValueList, tpe)) =>
                      val newTail = ListLiteral(functionValueList.tail, tpe)

                      if(after.length == functionValueList.length) { // No deletion.
                        Log("afterLength == functionValueList.length")
                        for{ pf <- repair(in.subExpr(argsIn(0)).withComputedValue(functionValueList.head), out.subExpr(after.head))
                             pf2 <- repair(in.subExpr(argsIn(1)).withComputedValue(newTail),
                               ListInsert(tpe, Nil, Nil, after.tail) combineWith out.formula) } yield {
                          ProgramFormula(ListLiteral.concat(
                            ListLiteral(inserted, tpe),
                            ListLiteral(List(pf.expr), tpe),
                            pf2.expr), pf.formula combineWith pf2.formula combineWith out.formula)
                        }
                      } else {
                        Log("afterLength < functionValueList.length")
                        assert(after.length < functionValueList.length) // some deletion happened.
                        val updatedOutProgram = ListInsert(tpe, Nil, Nil, after) combineWith out.formula // Recursive problem if
                        for{ pf <- repair(in.subExpr(argsIn(1)).withComputedValue(newTail), updatedOutProgram)} yield {
                          pf.wrap{ x =>
                            ListLiteral.concat(
                              ListLiteral(inserted, tpe),
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
                val updatedOutProgram = ListInsert(tpe, before.tail, inserted, after) combineWith out.formula

                for{pfHead <- repair(in.subExpr(argsIn(0)), out.subExpr(before.head))
                    pfTail <- repair(in.subExpr(argsIn(1)), updatedOutProgram)} yield {
                  ProgramFormula(ListLiteral.concat(ListLiteral(List(pfHead.expr), tpe), pfTail.expr),
                    pfHead.formula combineWith pfTail.formula
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

  private val InsertList = FreshIdentifier("insertList")
  def apply(tpe: Type, leftUnmodified: List[Expr], inserted: List[Expr], rightUnmodified: List[Expr]): ProgramFormula = {
    ProgramFormula(Expr(tpe, leftUnmodified, inserted, rightUnmodified))
  }

  def unapply(f: ProgramFormula): Option[(Type, List[Expr], List[Expr], List[Expr])] = {
    Expr.unapply(f.expr)
  }

  object Expr {
    def apply(tpe: Type, leftUnmodified: List[Expr], inserted: List[Expr], rightUnmodified: List[Expr]): Expr = {
      E(InsertList)(tpe)(
        ListLiteral(leftUnmodified, tpe),
        ListLiteral(inserted, tpe),
        ListLiteral(rightUnmodified, tpe),
        StringLiteral(".") // Not used direction
      )
    }

    def unapply(e: Expr): Option[(Type, List[Expr], List[Expr], List[Expr])] = {
      e match {
        case FunctionInvocation(InsertList, Seq(tpe0), Seq(
        ListLiteral(leftBefore, _),
        ListLiteral(inserted, tpe3),
        ListLiteral(rightBefore, _),
        _)) =>
          Some((tpe0, leftBefore, inserted, rightBefore))
        case _ => None
      }
    }
  }

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
