import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import inox.InoxProgram

import scala.reflect.ClassTag

/**
  * Created by Mikael on 03/03/2017.
  */
object ReverseProgram {
  type FunctionEntry = Identifier
  type ModificationSteps = Unit
  type OutExpr = Expr
  import Utils._
  import Constrainable._
  lazy val context = Context.empty.copy(options = Options(Seq(optSelectedSolvers(Set("smt-cvc4")))))

  /** Reverses a parameterless function, if possible.*/
  def put[A: Constrainable](out: A, prevOut: Option[OutExpr], modif: Option[ModificationSteps], prevIn: Option[(InoxProgram, FunctionEntry)]): Iterable[(InoxProgram, FunctionEntry)] = {
    val outExpr = inoxExprOf[A](out)
    implicit val symbols = defaultSymbols
    if(prevIn == None) {
      val main = FreshIdentifier("main")
      val fundef = mkFunDef(main)()(stp => (Seq(), outExpr.getType, _ => outExpr))
      return Stream((InoxProgram(context, Seq(fundef), allConstructors), main))
    }
    val (prevProgram, prevFunctionEntry) = prevIn.get
    val prevFunction = prevProgram.symbols.functions.getOrElse(prevFunctionEntry, return Nil)
    val prevBody = prevFunction.fullBody
    val newMain = FreshIdentifier("main")
    for {(newOutExpr, _) <- repair(prevBody, prevFunction.returnType, outExpr)
         newFunDef = mkFunDef(newMain)()(stp => (Seq(), prevFunction.returnType, _ => newOutExpr))
         newProgram = InoxProgram(context, Seq(newFunDef), allConstructors)
    } yield (newProgram, newMain)
  }

  @inline def castOrFail[A, B <: A](a: A): B =
    a.asInstanceOf[B]

  /** Will try its best to transform prevOutExpr so that it produces newOut or at least incorporates the changes.
    * @param function An expression that computed the value before newOut
    * @param newOut A *value* that prevOutExpr should produce
    **/
  def repair(function: Expr, functionType: Type, newOut: Expr)(implicit symbols: Symbols): Stream[(Expr, Map[Identifier, Expr])] = {
    if(function == newOut) return Stream((function, Map()))

    function match {
      case Let(vd@ValDef(id, tpe, flags), expr, body) =>
        for {(newBody, newAssignment) <- repair(body, functionType, newOut) // Later: Change assignments to constraints
              newValValue = newAssignment.getOrElse(id, expr)
             (newExpr, newAssignment2) <- repair(expr, tpe, newValValue)
              newFunction = Let(vd, newExpr, newBody)
              finalAssignments = (newAssignment ++ newAssignment2) - id
        } yield (newFunction, finalAssignments)

      case v@Variable(id, tpe, flags) =>
        newOut match {
          case l: Literal[_] =>
            if(symbols.isSubtypeOf(l.getType, tpe)) {
              Stream((v, Map(id -> l)))
            } else {
              throw new Error(s"How can we assign $l to $v of type $tpe ?")
            }

          case l@ADT(tpe2, args) =>
            if(symbols.isSubtypeOf(tpe2, tpe)) {
              Stream((v, Map(id -> l)))
            } else {
              throw new Error(s"How can we assign $l to $v of type $tpe ?")
            }
          case _ => throw new Exception(s"Don't know what to do: $v == $newOut")
        }

      case ADT(ADTType(tp, tpArgs), args) =>
        newOut match {
          case ADT(ADTType(tp2, tpArgs2), args2) if tp2 == tp && tpArgs2 == tpArgs => // Same type ! Maybe the arguments will change or move.
            if(args.length == 0) {
              return Stream((newOut, Map()))
            } // Now args.length > 0
            val adt = castOrFail[ADTDefinition, ADTConstructor](symbols.adts(tp))
            val tadt = adt.typed(tpArgs)
            val seqOfStreamSolutions = (args.zip(args2).zip(tadt.fields).map{ case ((aFun, aVal), avd) =>
              repair(aFun, avd.getType, aVal)
            })
            val streamOfSeqSolutions = inox.utils.StreamUtils.cartesianProduct(seqOfStreamSolutions)
            for{ seq <- streamOfSeqSolutions
                 reduced = ((List[Expr](), Map[Identifier, Expr]()) /: seq) { case ((ls, mm), (l, m)) => (l::ls, mm ++ m) } // TODO: Will be wrong in case of conflicts.
                 newArgs = reduced._1.reverse
                 assignments = reduced._2
            } yield {
              (ADT(ADTType(tp2, tpArgs2), newArgs), assignments)
            }
          case a => // Another value in the type hierarchy. But Maybe sub-trees are shared !

            ???
        }
      case _ => Stream((newOut, Map()))
    }
  }
}
