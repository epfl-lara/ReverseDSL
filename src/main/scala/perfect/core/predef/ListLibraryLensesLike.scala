package perfect.core
package predef

import scala.collection.mutable.ListBuffer

/**
  * Created by Mikael on 15/05/2017.
  */
trait ListLibraryLensesLike {
  self: ProgramUpdater
    with ContExps with Lenses with ListLensesLike
    with ListInsertLensesLike with InvocationLensesLike with ApplicationLensesLike =>

  trait ListLibraryOptions {
    /** In a map, can the output be transfered to the input, e.g. when adding a new row. */
    def canPushInsertedOutputToInput(output: Exp, lambda: Exp)(implicit symbols: Symbols): Boolean

    /** Returns an expression, the default value matching the first lambda argument's type */
    def extractLambdaDefaultArgument(e: Exp): Option[Exp]

    /** Returns an "unknown" fresh variable matching the type of the lambda's first argument */
    def extractLambdaUnknownVar(e: Exp): Option[Var]
  }

  /** Lense-like filter */
  class FilterLensLike(Application: ApplicationExtractor,
                       Invocation: InvocationExtractor,
                       ListLiteral: ListLiteralExtractor,
                       ListLibraryOptions: ListLibraryOptions)
    extends InvocationLensLike(Invocation) with FilterLike[Exp] { // TODO: Incorporate filterRev as part of the sources.
    def put(originalArgsValues: Seq[ContExp], newOutputProgram: ContExp, builder: Seq[Exp] => Exp)(implicit symbols: Symbols, cache: Cache): Stream[(Seq[ContExp], Cont)] = {
      val ContExp(lambda, lambdaF) = originalArgsValues.tail.head
      val newOutput = newOutputProgram.exp
      val ContExp(ListLiteral(originalInput, listBuilder), listF) = originalArgsValues.head
      //Log(s"FilterLens: $originalArgsValues => $newOutputProgram")
      val filterLambda = (expr: Exp) => lambdaF.assignments.flatMap(assign => maybeEvalWithCache(assign(Application(lambda, Seq(expr))))) contains ExpTrue
      newOutput match {
        case ListLiteral(newOutputList, _) =>
          filterRev(originalInput, filterLambda, newOutputList).map { (e: List[Exp]) =>
            (Seq(ContExp(listBuilder(e), listF.assignmentsAsOriginals), ContExp(lambda)), Cont())
          }
        case Var(v) => // Convert to a formula and return a new variable
          newOutputProgram.getFunctionValue match {
            case Some(ListLiteral(newOutputList, _)) =>
              filterRev(originalInput, filterLambda, newOutputList).map { (e: List[Exp]) =>
                (Seq(ContExp(listBuilder(e), listF.assignmentsAsOriginals), ContExp(lambda)), Cont())
              }
            case _ =>
              val newVar = freshen(v)
              Stream(((Seq(ContExp(newVar), ContExp(lambda)),
                newOutputProgram.context combineWith listF.assignmentsAsOriginals combineWith Cont(Map(), builder(Seq(newVar, lambda)) === newOutput))))
          }

        case _ => Stream.empty // We don't know what to do.
      }
    }
  }

  // TODO: Merge these two functions
  // The first context is Cont is for the lambda, the second is for the arguments
  def expand(i: List[Stream[Either[(Exp, Cont), ((Exp, Exp), Cont)]]], lambda: Exp)(implicit symbols: Symbols):
  Stream[(List[Exp], Exp, Cont, Cont)] = {
    for {e <- Utils.StreamUtils.cartesianProduct(i)
         (argumentsChanged, argFormulas, newLambdas) = createArgumentsChanged(e, lambda)
         (lExpr, lFormula) <- newLambdas
    } yield {
      (argumentsChanged, lExpr, lFormula, argFormulas)
    }
  }

  private def recombineArgumentsLambdas(lambda: Exp, listBuilder: List[Exp] => Exp)
                                       (e: List[Either[(Exp, Cont), ((Exp, Exp), Cont)]])(implicit symbols: Symbols)
  : Stream[(Seq[ContExp], Cont)] = {
    //    Log(s"recombineArgumentLambdas($e)")
    val (argumentsChanged, argFormulas, newLambdas) = createArgumentsChanged(e, lambda)
    for {l <- newLambdas
         (lExpr, lFormula) = l
    } yield {
      (Seq(ContExp(listBuilder(argumentsChanged), argFormulas), ContExp(lExpr, lFormula combineWith argFormulas)), Cont())
    }
  }

  private def createArgumentsChanged(e: List[Either[(Exp, Cont), ((Exp, Exp), Cont)]], lambda: Exp) = {
    (e.map {
      case Left((e, _)) => e
      case Right(((e, _), _)) => e
    },
      Cont(e.collect { case Left((_, f)) => f case Right((_, f)) => f }),
      createNewLamdas(lambda, e)
    )
  }

  private def createNewLamdas(lambda: Exp, e: List[Either[(Exp, Cont), ((Exp, Exp), Cont)]]) = {
    // If there is at least one modified lambda, we collect all changed lambdas.
    // If not we return at least one lambda.
    if (e.view.exists(_.isInstanceOf[Right[_, _]])) {
      e.collect { case Right(((expr, lambda), context)) => (lambda, context) }.toStream
    } else Stream((lambda, Cont()))
  }

  /** Lense-like map, with the possibility of changing the mapping lambda. */
  class MapLensLike(Application: ApplicationExtractor,
                    Invocation: InvocationExtractor,
                    ListLiteral: ListLiteralExtractor,
                    ListInsertLensGoal: ListInsertLensGoalExtractor,
                    ListLibraryOptions: ListLibraryOptions) extends InvocationLensLike(Invocation) {

    import ListLibraryOptions._

    def put(originalArgsValues: Seq[ContExp], out: ContExp, builder: Seq[Exp] => Exp)(implicit symbols: Symbols, cache: Cache): Stream[(Seq[ContExp], Cont)] = {
      //Log(s"map.apply($newOutput)")
      val ContExp(lambda, lambdaF) = originalArgsValues.tail.head
      val ContExp(ListLiteral(originalInput, listBuilder), listF) = originalArgsValues.head
      val valueByDefault = originalInput.headOption.getOrElse(extractLambdaDefaultArgument(lambda).getOrElse(return Stream.empty))
      // Maybe we change only arguments. If not possible, we will try to change the lambda.

      out.exp match {
        /*case TreeModification(tpeGlobal, tpeLocal, originalOutputModifList, modified, argsInSequence) =>
          val ListLiteral(originalOutputModifList2, listBuilder) = originalOutputModifList
          val (index, remaining) = argsInSequence.span(_ == Utils.tail)
          val original = originalInput(index.length)
          val newVar = Variable(FreshIdentifier("x"), argType, Set())

          if(remaining.isEmpty) { // TODO: Case not supported yet, we currently have to end with "head" selection.
            Stream.empty
          } else {
            repair(ContExp(Application(lambda, Seq(original))),
              newOutput.subExpr(TreeModification.Goal(tpeGlobal, tpeLocal, originalOutputModifList2(index.length), modified, remaining.tail))) map {
              case pf@ContExp(Application(lExpr, Seq(expr2)), formula2) =>
                val lambda2 = castOrFail[Exp, Lambda](lExpr)
                if (lambda2 != lambda && expr2 == original) {
                  (Seq(TreeModification(ADTType(Utils.cons, Seq(argType)),
                    tpeLocal,
                    originalArgsValues.head.exp,
                    expr2,
                    index :+ Utils.head
                  ) combineWith formula2 combineWith originalArgsValues.head.context, ContExp(lambda2, formula2)), Cont())
                } else {
                  (Seq(TreeModification(ADTType(Utils.cons, Seq(argType)),
                    tpeLocal,
                    originalArgsValues.head.exp,
                    expr2,
                    index :+ Utils.head
                  ) combineWith formula2 combineWith originalArgsValues.head.context, ContExp(lambda)), Cont())
                }
            }
          }*/


        case ListInsertLensGoal(before, inserted, after, listBuilder, listInsertLensGoalBuilder) =>
          // Beware, there might be changes in before or after. But at least, we know how the insertion occurred.
          val (newBeforeAfter: List[Stream[Either[(Exp, Cont), ((Exp, Exp), Cont)]]]) =
            (before.zip(originalInput.take(before.length)) ++
              after.zip(originalInput.drop(originalInput.length - after.length))).map {
              case (expr, original) =>
                if (isValue(expr)) {
                  Stream(Left[(Exp, Cont), ((Exp, Exp), Cont)]((original, Cont())))
                } else {
                  repair(ContExp(Application(lambda, Seq(original))), out.subExpr(expr)).map {
                    case pf@ContExp(Application(lExpr, Seq(expr2)), formula2) =>
                      val lambda2 = lExpr
                      if (lambda2 != lambda && expr2 == original) {
                        Right[(Exp, Cont), ((Exp, Exp), Cont)](((expr2, lambda2), formula2))
                      } else if (lambda2 != lambda && expr2 != expr) {
                        throw new Exception(s"Don't know how to invert both the lambda and the value: $lambda2 != $lambda, $expr2 != $expr")
                      } else {
                        Left[(Exp, Cont), ((Exp, Exp), Cont)]((expr2, formula2))
                      }
                    case e =>
                      throw new Exception(s"I don't know how to deal with this replacement: $e")
                  }
                }
            }
          assert(inserted.forall { x => isValue(x) }, s"not all inserted elements were values $inserted")

          // Inserted does not change the lambda normally
          val newInserted: List[Stream[Either[(Exp, Cont), ((Exp, Exp), Cont)]]] = {
            // We have no choice but to repair the lambda to see what would be the original value for each of the newly added elements.
            // The valueByDefault is just a copy of neighbor values if it exists, else it is a value

            val (Seq(expr), newFormula) = {
              val unknown = extractLambdaUnknownVar(lambda).getOrElse(return Stream.empty)
              (Seq(unknown), Cont(unknown -> OriginalValue(valueByDefault)))
            }
            inserted.map { i =>
              (if (canPushInsertedOutputToInput(i, lambda)) { // An empty string ltteral was added. First we suppose that it was inserted in the original elements
                Stream(Left((i, Cont())))
              } else Stream.empty) #:::
                repair(ContExp(Application(lambda, Seq(expr)), newFormula), ContExp(i)).flatMap {
                  case pf@ContExp(Application(lExpr, Seq(expr2)), formula2) =>
                    List(Left(expr2, formula2): Either[(Exp, Cont), ((Exp, Exp), Cont)])
                }
            }
          }

          for {newBeforeAfterInsertedUniqueFormula <- expand(newBeforeAfter ++ newInserted, lambda)
               (newBeforeAfterUnique, newLambda, formulaLambda, formulaArg) = newBeforeAfterInsertedUniqueFormula
               (newBefore, newAfterInserted) = newBeforeAfterUnique.splitAt(before.length)
               (newAfter, newInsertedRaw) = newAfterInserted.splitAt(after.length)} yield {
            // A list insert results in a list insert in the argument.
            val firstArg = ContExp(listInsertLensGoalBuilder(
              newBefore,
              newInsertedRaw,
              newAfter
            ), formulaArg combineWith listF.assignmentsAsOriginals)
            val secondArg = ContExp(newLambda, formulaLambda combineWith lambdaF.assignmentsAsOriginals)

            (Seq(firstArg, secondArg), Cont())
          }
        case _ =>
          val mapr = new MapReverseLike[(Exp, Cont), Exp, ((Exp, Exp), Cont)] {
            override def f = (exprF: (Exp, Cont)) => lambdaF.assignments.flatMap(assign => maybeEvalWithCache(assign(Application(lambda, Seq(exprF._1))))).getOrElse(throw new Exception(s"Could not evaluate $exprF"))

            override def fRev = (prevIn: Option[(Exp, Cont)], elemOut: Exp) => {
              //Log(s"Map.fRev: $prevIn, $out")
              extractLambdaUnknownVar(lambda) match {
                case Some(unknownVar) =>
                  val (Seq(in), newFormula) =
                    prevIn.map(x => (Seq(x._1), x._2)).getOrElse {
                      (Seq(unknownVar), Cont(unknownVar -> OriginalValue(valueByDefault)))
                    }
                  //Log(s"in:$in\nnewformula:$newFormula")
                  //Log.prefix(s"fRev($prevIn, $out)=") :=
                  repair(ContExp(Application(lambda, Seq(in)), newFormula combineWith lambdaF).wrappingLowPriority(), out.subExpr(elemOut)).flatMap {
                    case ContExp(Application(lambda2, Seq(in2)), context)
                      if lambda2 == lambda => //The argument's values have changed
                      Stream(Left((in2, context)))
                    case ContExp(Application(lambda2Expr, Seq(in2)), context) =>
                      // In the case when in2 is now a variable, we add the constraint that it should equal the original variable.
                      Stream(Right(((in2, lambda2Expr), context)))
                    case e@ContExp(app, f) =>
                      Stream.empty
                    //                   throw new Exception(s"[Internal error] Don't know how to handle: $e")
                    // We remove those which only return the valueByDefault
                  }
                case _None => Stream.empty
              }
            }
          }

          //Log(s"Reversing $originalArgs: $originalOutput => $newOutput")
          val res = mapr.mapRev((originalInput.map(x => (x, listF))),
            ListLiteral.unapply(out.getFunctionValue.getOrElse(return Stream.empty)).get._1)
          //Log("intermediate: "+res)
          res.flatMap(recombineArgumentsLambdas(lambda, listBuilder)) // /: Log.intermediate_recombined
      }
    }
  }


  /** Lense-like map, with the possibility of changing the mapping lambda. */
  class FlatMapLensLike(Application: ApplicationExtractor,
                        Invocation: InvocationExtractor,
                        ListLiteral: ListLiteralExtractor,
                        ListInsertLensGoal: ListInsertLensGoalExtractor,
                        ListLibraryOptions: ListLibraryOptions) extends InvocationLensLike(Invocation) {
    import ListLibraryOptions._
    def put(originalArgsValues: Seq[ContExp], newOutput: ContExp, builder: Seq[Exp] => Exp)(implicit symbols: Symbols, cache: Cache): Stream[(Seq[ContExp], Cont)] = {
      val originalInputProg@ContExp(originalInputExp, originalInputF) = originalArgsValues.head
      val (originalInput, listBuilder) = ListLiteral.unapply(originalInputExp).getOrElse(return Stream.empty)
      val ContExp(lambda, lambdaF) = originalArgsValues.tail.head

      val (outValue, outBuilder) = ListLiteral.unapply(newOutput.exp).getOrElse(return Stream.empty)
      val valueByDefault = originalInput.headOption.getOrElse(extractLambdaDefaultArgument(lambda).getOrElse(return Stream.empty))

      val fmapr = new FlatMapReverseLike[(Exp, Cont), Exp, ((Exp, Exp), Cont)] {
        def f: ((Exp, Cont)) => List[Exp] = { (exprF: (Exp, Cont)) =>
          val ListLiteral(l, _) = maybeEvalWithCache(lambdaF.assignments.get(Application(lambda, Seq(exprF._1)))).getOrElse(throw new Exception(s"Could not evaluate $exprF"))
          l
        }

        def fRev: (Option[(Exp, Cont)], List[Exp]) => Stream[Either[(Exp, Cont), ((Exp, Exp), Cont)]] = { (prevIn, out) =>
          extractLambdaUnknownVar(lambda) match {
            case None => Stream.empty
            case Some(unknownVar) =>
              val (Seq(in), newCont) =
                prevIn.map(x => (Seq(x._1), x._2)).getOrElse {
                  (Seq(unknownVar), Cont(unknownVar -> OriginalValue(valueByDefault)))
                }
              //Log(s"flatmap in:$in\nnewformula:$newCont")
              //Log.res :=
              repair(ContExp(Application(lambda, Seq(in)), newCont), newOutput.subExpr(outBuilder(out))).flatMap {
                case ContExp(Application(lambda2, Seq(in2)), formula)
                  if lambda2 == lambda => //The argument's values have changed
                  Stream(Left((in2, formula)))
                case ContExp(Application(lambda2, Seq(in2)), formula) =>
                  // In the case when in2 is now a variable, we add the constraint that it should equal the original variable.
                  Stream(Right(((in2, lambda2), formula)))
                case e@ContExp(app, f) =>
                  throw new Exception(s"Don't know how to invert both the lambda and the value: $e")
              }
          }
        }
      }
      fmapr.flatMapRev(originalInput.map(x => (x, originalInputF)), outValue).flatMap(recombineArgumentsLambdas(lambda, listBuilder))
    }
  }
}

