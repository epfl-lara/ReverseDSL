import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import inox.InoxProgram
import inox.evaluators.EvaluationResults

import scala.collection.mutable
import scala.reflect.ClassTag

/**
  * Created by Mikael on 03/03/2017.
  */
object ReverseProgram {
  type FunctionEntry = Identifier
  type ModificationSteps = Unit
  type OutExpr = Expr
  type Cache = mutable.HashMap[Expr, Expr]
  import Utils._
  import Constrainable._
  lazy val context = Context.empty.copy(options = Options(Seq(optSelectedSolvers(Set("smt-cvc4")))))
  implicit val symbols = defaultSymbols

  /** Reverses a parameterless function, if possible.*/
  def put[A: Constrainable](out: A, prevOut: Option[OutExpr], modif: Option[ModificationSteps], prevIn: Option[(InoxProgram, FunctionEntry)]): Iterable[(InoxProgram, FunctionEntry)] = {
    val outExpr = inoxExprOf[A](out)
    if(prevIn == None) {
      val main = FreshIdentifier("main")
      val fundef = mkFunDef(main)()(stp => (Seq(), outExpr.getType, _ => outExpr))
      return Stream((InoxProgram(context, Seq(fundef), allConstructors), main))
    }
    val (prevProgram, prevFunctionEntry) = prevIn.get
    val prevFunction = prevProgram.symbols.functions.getOrElse(prevFunctionEntry, return Nil)
    val prevBody = prevFunction.fullBody
    val newMain = FreshIdentifier("main")
    implicit val cache = new mutable.HashMap[Expr, Expr]
    for {(newOutExpr, _) <- repair(prevBody, prevFunction.returnType, outExpr, e => e)
         newFunDef = mkFunDef(newMain)()(stp => (Seq(), prevFunction.returnType, _ => newOutExpr))
         newProgram = InoxProgram(context, Seq(newFunDef), allConstructors)
    } yield (newProgram, newMain)
  }

  /** Eval function. Uses a cache normally*/
  def evalWithCache(expr: Expr)(implicit cache: Cache) = cache.getOrElseUpdate(expr, {
    val funDef = mkFunDef(FreshIdentifier("main"))()(stp => (Seq(), expr.getType, _ => expr))
    val prog = InoxProgram(context, Seq(funDef), allConstructors)
    prog.getEvaluator.eval(expr) match {
      case EvaluationResults.Successful(e) => e
      case m => throw new Exception(s"Could not evaluate: $expr, got $m")
    }
  })

  @inline def castOrFail[A, B <: A](a: A): B =
    a.asInstanceOf[B]

  /** Will try its best to transform prevOutExpr so that it produces newOut or at least incorporates the changes.
    * @param function An expression that computed the value before newOut
    * @param newOut A *value* that prevOutExpr should produce
    **/
  def repair(function: Expr, functionType: Type, newOut: Expr, letPrevAssignments: Expr => Expr)(implicit symbols: Symbols, cache: Cache): Stream[(Expr, Map[ValDef, Expr])] = {
    if(function == newOut) return Stream((function, Map()))

    function match {
      case Let(vd@ValDef(id, tpe, flags), expr, body) =>
        for {(newBody, newAssignment) <- repair(body, functionType, newOut, ((x: Expr) => Let(vd, expr, x)) andThen letPrevAssignments ) // Later: Change assignments to constraints
              newValValue = newAssignment.getOrElse(vd, expr)
             (newExpr, newAssignment2) <- repair(expr, tpe, newValValue, letPrevAssignments)
              newFunction = Let(vd, newExpr, newBody)
              finalAssignments = (newAssignment ++ newAssignment2) - vd
        } yield (newFunction, finalAssignments)

      case v@Variable(id, tpe, flags) =>
        Stream((v, Map(v.toVal -> newOut))) // newOut should be a value

      case ADT(ADTType(tp, tpArgs), args) =>
        newOut match {
          case ADT(ADTType(tp2, tpArgs2), args2) if tp2 == tp && tpArgs2 == tpArgs => // Same type ! Maybe the arguments will change or move.
            if(args.length == 0) {
              return Stream((newOut, Map()))
            } // Now args.length > 0
            val adt = castOrFail[ADTDefinition, ADTConstructor](symbols.adts(tp))
            val tadt = adt.typed(tpArgs)
            val seqOfStreamSolutions = (args.zip(args2).zip(tadt.fields).map{ case ((aFun, aVal), avd) =>
              repair(aFun, avd.getType, aVal, letPrevAssignments).map((_, avd, () => evalWithCache(letPrevAssignments(aFun))))
            })
            val streamOfSeqSolutions = inox.utils.StreamUtils.cartesianProduct(seqOfStreamSolutions)
            for{ seq <- streamOfSeqSolutions
                 reduced = ((List[Expr](), Map[ValDef, Expr]()) /: seq) {
                   case ((ls, mm), ((l, m), field, recompute)) =>
                     if((mm.keys.toSet intersect m.keys.toSet).nonEmpty) { // TODO: Rewrite this so that we discard values which did not changed in the intersection.
                       println("Warning: Merging following assignments")
                       println(mm)
                       println(m)
                       val realValue = evalWithCache(letPrevAssignments(m.keys.head.toVariable))
                       println(s"Real value of ${m.keys.head}: $realValue")
                       println(s"Value which was going to update: ${m(m.keys.head)}")
                       if(realValue == m(m.keys.head)) { // The value did not change ! We shall not put it in the assignment map.
                         (l::ls, mm)
                       } else {
                         (l::ls, mm ++ m)
                       }
                     } else {
                       (l::ls, mm ++ m)
                     }
                 } // TODO: Will be wrong in case of conflicts. Need to replace only changed values.
                 newArgs = reduced._1.reverse
                 assignments = reduced._2
            } yield {
              (ADT(ADTType(tp2, tpArgs2), newArgs), assignments)
            }
          case ADT(ADTType(tp2, tpArgs2), args2) => // Maybe the newOut just wrapped the previous value of function
            val functionValue = evalWithCache(letPrevAssignments(function))

            // Check if the old value is inside the new value, in which case we add a wrapper.
            if(exprOps.exists{
              case t if t == functionValue => true
              case _ => false
            }(newOut)) {
              // We wrap the computation of functionValue with ADT construction

              val newFunction = exprOps.postMap{
                case t if t == functionValue => Some(function)
                case _ => None
              }(newOut)

              Stream((newFunction, Map()))
            } else {
              println(s"After evaluation, got $functionValue")
              println(s"Original program $function")
              println(s"Wanting to plug-in $newOut")
              ???
            }

          case a => // Another value in the type hierarchy. But Maybe sub-trees are shared !

            ???
        }
      case _ => Stream((newOut, Map()))
    }
  }
}