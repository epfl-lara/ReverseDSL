package perfect

import inox.Identifier
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import scala.collection.mutable
import inox.evaluators._

/**
  * Created by Mikael on 03/03/2017.
  */
object ReverseProgramDirect {
  type FunctionEntry = Identifier
  type ModificationSteps = Unit
  type OutExpr = Expr
  type Cache = mutable.HashMap[Expr, Expr]
  type Formula = Map[ValDef, Expr] // The assignments and the formula containing the other expressions.

  import Utils._
  import InoxConvertible._
  lazy val context = Context.empty.copy(options = Options(Seq(optSelectedSolvers(Set("smt-cvc4")))))
  implicit val symbols = defaultSymbols

  /** Reverses a parameterless function, if possible.*/
  def put[A: InoxConvertible](out: A, prevOut: Option[OutExpr], modif: Option[ModificationSteps], prevIn: Option[(InoxProgram, FunctionEntry)]): Iterable[(InoxProgram, FunctionEntry)] = {
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
    for {(newOutExpr, _) <- repair(prevBody, Map(), prevFunction.returnType, outExpr)
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

  private case class letm(v: Map[ValDef, Expr]) {
    @inline def in(res: Expr) = {
      (res /: v) {
        case (res, (key, value)) => let(key, value)(_ => res)
      }
    }
  }

  @inline def castOrFail[A, B <: A](a: A): B =
    a.asInstanceOf[B]

  def defaultValue(t: Type)(implicit symbols: Symbols): Expr = {
    import inox._
    import inox.trees._
    import inox.trees.dsl._
    import inox.solvers._
    t match {
      case StringType => StringLiteral("#")
      case Int32Type => IntLiteral(42)
      case IntegerType => IntegerLiteral(BigInt(86))
      case BooleanType => BooleanLiteral(true)
      case t: ADTType =>
        val tid = t.id
        val tps = t.tps
        symbols.adts(tid) match {
          case e: ADTConstructor =>
            ADT(t, e.typed(tps).fields.map(x => defaultValue(x.getType)))
          case e: ADTSort => // Choose the smallest non-recursive value if possible. This is an heuristic but works in our cases.
            val mainConstructor = e.constructors.sortBy { constructor =>
              constructor.typed(tps).fields.map {
                case s => if (s.getType == t) 10 else
                  if (ADTType(t.getADT.definition.root.id, tps) == s.getType) 5
                else 0
              }.sum
            }.head
            defaultValue(ADTType(mainConstructor.id, tps))
        }
    }
  }

  /** Will try its best to transform prevOutExpr so that it produces newOut or at least incorporates the changes.
    * Basically, we solve the problem:
    *  let variables = values in function = newOut
    * by trying to change the variables values, or the function body itself.
    *
    * @param function An expression that computed the value before newOut
    * @param currentValues Values from which function depends, with theyr original values.
    * @param functionType The declared return type of the function
    * @param newOut A *value* that prevOutExpr should produce
    * @return A set of possible expressions, along with a set of possible assignments to input variables.
    **/
  def repair(function: Expr, currentValues: Map[ValDef, Expr], functionType: Type, newOut: Expr)(implicit symbols: Symbols, cache: Cache): Stream[(Expr, Formula)] = {
    //println(s"\n@solving ${currentValues.map{ case (k, v) => s"val ${k.id} = $v\n"}.mkString("")}$function = $newOut")
    if(function == newOut) return { //println("@return original");
      Stream((function, Map()))
    }

    lazy val functionValue = evalWithCache(letm(currentValues) in function) // TODO: Optimize this ?

    {
      functionType match {
        case a: ADTType =>
          function match {
            case l: Let => Stream.empty[(Expr, Map[ValDef, Expr])] // No need to wrap a let expression, we can always do this later. Indeed,
              //f{val x = A; B} = {val x = A; f(B)}
            case _ =>
              maybeWrap(function, newOut, functionValue) #::: maybeUnwrap(function, newOut, functionValue)
          }
        case _ => Stream.empty[(Expr, Map[ValDef, Expr])]
      }
    } #::: {
      val res: Stream[(Expr, Map[ValDef, Expr])] = function match {
        // Values (including lambdas) should be immediately replaced by the new value
        case l: Literal[_] => Stream((newOut, Map()))
        case lFun@Lambda(vd, body) => // Check for closures, i.e. free variables.
          val freeVars = exprOps.variablesOf(body).map(_.toVal) -- vd
          if(freeVars.isEmpty) {
            Stream((newOut, Map()))
          }  else {
            // We need to determine the values of these free variables.
            newOut match {
              case Lambda(vd2, body2) =>
                val dummyInputs = vd.map{ v =>
                  v -> defaultValue(v.getType)
                }.toMap
                for{(newBody, newAssignments) <- repair(body, dummyInputs ++ freeVars.map(fv => fv -> currentValues(fv)).toMap, lFun.getType, body2)
                  newFreevarAssignments = freeVars.map(fv => fv -> newAssignments.getOrElse(fv, currentValues(fv))).toMap }
                  yield {
                    (Lambda(vd, newBody): Expr, newFreevarAssignments)
                  }
              case _ => ???
            }
          }

        // Variables are assigned the given value.
        case v@Variable(id, tpe, flags) =>
          Stream((v, Map(v.toVal -> newOut)))

        // Let expressions eval their variable, reverse their body and then their assigning expression
        // It comes from the fact that
        // let x = b in c[x]    is equivalent to      Application((\x. c[x]), (b))
        // In theory with rewriting it could be dropped, but
        case Let(vd@ValDef(id, tpe, flags), expr, body) =>
          val currentVdValue = evalWithCache(letm(currentValues) in expr)

          for {(newBody, newAssignment) <- repair(body, currentValues + (vd -> currentVdValue), functionType, newOut) // Later: Change assignments to constraints
               newValValue = newAssignment.getOrElse(vd, expr)
               (newExpr, newAssignment2) <- repair(expr, currentValues, tpe, newValValue)
               newFunction = Let(vd, newExpr, newBody)
               finalAssignments = (newAssignment ++ newAssignment2) - vd
          } yield (newFunction, finalAssignments)

/*        case StringConcat(expr1, expr2) =>
          val tmp = ValDef(FreshIdentifier("t"), StringType, Set())
          repair(_Tuple2(expr1, expr2),

            StringConcat(i.getField(_1), i.getField(_2)) === o)*/

        case ADT(ADTType(tp, tpArgs), args) =>
          newOut match {
            case ADT(ADTType(tp2, tpArgs2), args2) if tp2 == tp && tpArgs2 == tpArgs => // Same type ! Maybe the arguments will change or move.
              if (args.length == 0) {
                return {
                  //println("@return original");
                  Stream((newOut, Map()))
                }
              }
              // Now args.length > 0
              val adt = castOrFail[ADTDefinition, ADTConstructor](symbols.adts(tp))
              val tadt = adt.typed(tpArgs)
              val seqOfStreamSolutions = (args.zip(args2).zip(tadt.fields).map { case ((aFun, aVal), avd) =>
                repair(aFun, currentValues, avd.getType, aVal).map((_, avd, () => evalWithCache(letm(currentValues) in aFun)))
              })
              val streamOfSeqSolutions = inox.utils.StreamUtils.cartesianProduct(seqOfStreamSolutions)
              for {seq <- streamOfSeqSolutions
                   reduced = combineResults(seq, currentValues)
                   newArgs = reduced._1.reverse
                   assignments = reduced._2
              } yield {
                (ADT(ADTType(tp2, tpArgs2), newArgs), assignments)
              }
            case ADT(ADTType(tp2, tpArgs2), args2) => // Maybe the newOut just wrapped the previous value of function
              Stream.empty

            case a => // Another value in the type hierarchy. But Maybe sub-trees are shared !
              throw new Exception(s"Don't know how to handle this case : $a is supposed to be put in place of a ${tp}")
          }

        case m@Application(lambdaExpr, arguments) =>
          val originalValue = lambdaExpr match {
            case v: Variable => currentValues.getOrElse(v.toVal, evalWithCache(letm(currentValues) in v))
            case l: Lambda => evalWithCache(letm(currentValues) in l)
          }
          originalValue match {
            case l@Lambda(argNames, body) =>
              val argumentValues = argNames.zip(arguments.map(arg => evalWithCache(letm(currentValues) in arg))).toMap
              for { (newBody, assignments) <- repair(body, argumentValues, l.getType, newOut) // TODO: Incorporate changes in lambdas.
                    newArgumentsAssignments <- inox.utils.StreamUtils.cartesianProduct(arguments.zip(argNames).map { case (arg, v) =>
                     repair(arg, currentValues, v.getType, assignments.getOrElse(v, argumentValues(v)))
                   })
                   newArguments = newArgumentsAssignments.map(_._1)
                   isSameBody = newBody == body
                   newLambda = if (isSameBody) l else Lambda(argNames, newBody)
                   (newAppliee, assignments2) <- lambdaExpr match {
                     case v: Variable => Stream(v -> (if(isSameBody) Map() else Map(v.toVal -> newLambda)))
                     case l: Lambda => repair(lambdaExpr, currentValues, l.getType, newLambda)
                   }
                   finalApplication = Application(newAppliee, newArguments)
                   newAssignments = Map[ValDef, Expr]() ++ assignments2 ++
                     newArgumentsAssignments.flatMap(_._2.toList) // TODO: Deal with variable value merging like above.
              } yield {
                (finalApplication: Expr, newAssignments)
              }
            case _ => throw new Exception(s"Don't know how to handle this case : $m of type ${m.getClass.getName}")
          }

        case anyExpr =>
          println(s"Don't know how to handle this case : $anyExpr of type ${anyExpr.getClass.getName},\nIt evaluates to:\n$functionValue\nand I will try to wrap it to match $newOut")
          Stream.empty
      }
      res
    }
  }

  private def combineResults(seq: List[((Expr, Map[ValDef,Expr]), ValDef, () => inox.trees.Expr)], currentValues: Map[ValDef,Expr])
            (implicit symbols: Symbols, cache: Cache) =
    ((List[Expr](), Map[ValDef, Expr]()) /: seq) {
    case ((ls, mm), ((l, m), field, recompute)) =>
      if ((mm.keys.toSet intersect m.keys.toSet).nonEmpty && {
        // Compare new assignment with the original value.
        val realValue = evalWithCache(letm(currentValues) in m.keys.head.toVariable)
        realValue == m(m.keys.head)
      }) {
        // The value did not change ! We shall not put it in the assignment map.
        (l :: ls, mm)
      } else (l :: ls, mm ++ m)
  }

  private def maybeWrap(function: Expr, newOut: Expr, functionValue: Expr): Stream[(Expr, Map[ValDef, Expr])] = {
    // Checks if the old value is inside the new value, in which case we add a wrapper.
    if (exprOps.exists {
      case t if t == functionValue => true
      case _ => false
    }(newOut)) {
      // We wrap the computation of functionValue with ADT construction

      val newFunction = exprOps.postMap {
        case t if t == functionValue => Some(function)
        case _ => None
      }(newOut)

      Stream((newFunction, Map()))
    } else {
      Stream.empty
    }
  }

  // Should be called on functions ADT only.
  private def maybeUnwrap(function: Expr, newOut: Expr, functionValue: Expr): Stream[(Expr, Map[ValDef, Expr])] = {
    if(functionValue == newOut) return Stream((function, Map()))

    (function, functionValue) match {
      case (ADT(ADTType(tp, tpArgs), args), ADT(ADTType(tp2, tpArgs2), argsValue)) =>
        // Checks if the old value is inside the new value, in which case we add a wrapper.
        argsValue.toStream.zipWithIndex.filter{ case (arg, i) =>
          exprOps.exists {
            case t if t == newOut => true
            case _ => false
          }(arg)
        }.flatMap{ case (arg, i) =>
          maybeUnwrap(args(i), newOut, arg)
        }

      case _ => Stream.empty
    }
  }
}
