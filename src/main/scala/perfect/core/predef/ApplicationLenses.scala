package perfect.core
package predef

/**
  * Created by Mikael on 10/05/2017.
  */
trait ApplicationLenses { self: ProgramUpdater with ContExps with Lenses with LambdaLenses =>
  def buildApplication(lambda: Exp, args: Seq[Exp]): Exp
  def extractApplication(e: Exp): Option[(Exp, Seq[Exp])]

  object Application {
    def apply(lambda: Exp, args: Seq[Exp]): Exp = buildApplication(lambda, args)
    def unapply(e: Exp): Option[(Exp, Seq[Exp])] = extractApplication(e)
  }

  object ApplicationLens extends SemanticLens {
    isPreemptive = true
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = in.exp match {
      case Application(lambdaExpr, arguments) => // TODO: Put this into a lense.
        val originalValueMaybe: Option[Exp] = in.subExpr(lambdaExpr).simplifiedExpr match {
          case l@Lambda(_, _, _) => Some(l)
          //case _ => throw new Exception("Don't know how to deal with an application over non-lambda: "+lambdaExpr)
          case l => in.context.partialAssignments.flatMap(assign => maybeEvalWithCache(assign._1(l)))
        } // /: Log.Original_Value

        // Returns the new list of arguments plus a mapping from old to new values.
        def freshenArgsList(argNames: Seq[Var]): (Seq[Var], Map[Var, Var], Map[Var, Var]) = {
          val freshArgsNames = argNames.map(vd => freshen(vd))
          val oldToFresh = argNames.zip(freshArgsNames).toMap
          val freshToOld = freshArgsNames.zip(argNames).toMap
          (freshArgsNames, oldToFresh, freshToOld)
        }

        originalValueMaybe match {
          case Some(originalValue@Lambda(argNames, body, lambdaBuilder)) =>
            val (freshArgsNames, oldToFresh, freshToOld) = freshenArgsList(argNames)
            @inline def renew(e: Exp) = replaceFromVars(oldToFresh, e)
            @inline def back(e: Exp) = replaceFromVars(freshToOld, e)
            object Back { def unapply(e: KnownValue) = Some(e.map(back)) }

            val freshBody = renew(body)
            val assignments = in.context.assignments
            val argumentVals =
              arguments.map( arg =>
                assignments.flatMap(assign => maybeEvalWithCache(assign(arg)).map(v => OriginalValue(v)))
              )

            if(argumentVals.forall(_.nonEmpty)) {
              val argumentValues = freshArgsNames.zip(argumentVals.map(_.get)).toMap
              val newpf = (in.subExpr(freshBody) combineWith Cont(argumentValues)).wrappingEnabled

              def backPf(newBodyFresh: Exp, newBodyFreshCont: Cont): Exp = {
                val toInline = newBodyFreshCont.known.collect{
                  case (k, v@Back(newv)) if newv != v => k -> newv.getValue.get
                }
                preMap({
                  case Var(v) => toInline.get(v)
                  case _ => None
                }, true)(back(newBodyFresh)) // /: Log.prefix(s"backpf($newBodyFresh, $newBodyFreshCont) = ")
              }

              for {pf <- repair(newpf, out)
                   ContExp(newBodyFresh, newBodyCont) = pf
                   newBody = backPf(newBodyFresh, newBodyCont)
                   isSameBody = newBody == body // /: Log.isSameBody
                   args <- ContExp.regroupArguments(arguments.zip(freshArgsNames).map { case (arg, expected) =>
                     repair(in.subExpr(arg), out.subExpr(expected) combineWith newBodyCont combineWith Cont(expected -> argumentValues(expected)))
                   })
                   (newArguments, newArgumentsCont) = args
                   newLambda = if (isSameBody) originalValue else Lambda(argNames, newBody)
                   pfLambda <- lambdaExpr match {
                     case Var(v) => Stream(ContExp(v, if (isSameBody) Cont() else
                       Cont(v -> StrongValue(newLambda))))
                     case l => repair(ContExp(l, in.context),
                       out.subExpr(newLambda) combineWith newBodyCont)
                   }
                   ContExp(newAppliee, lambdaRepairCont) = pfLambda
                   finalApplication = Application(newAppliee, newArguments)
              } yield {
                val varsToRemove = freshArgsNames.filter{ v => !exists{ case `v` => true case _ => false}(finalApplication)}
                val combinedCont = newBodyCont combineWith lambdaRepairCont combineWith
                  newArgumentsCont removeArgs varsToRemove
                ContExp(finalApplication: Exp, combinedCont)
              }
            } else { // Some argument's values are not known, we try unification
              // We can influcence only the variables's values which do not appear in output
              // We try to set up all known variables to their values except for one.
              val originalVariables = in.freeVars.filter(x => in.context.findConstraintValue(x).nonEmpty)
              // We try to evaluate the in.expr or evaluate all the arguments.
              lambdaExpr match {
                case Var(v) if (originalVariables contains v) &&
                  !arguments.exists(arg => exists{ case Var(v2) if v2 == v => true  case _ => false}(arg)) => // The variable should not be used in arguments.
                  def modifyFunction: Stream[ContExp] = { //The caller is a variable not used in arguments
                    if (originalVariables.size == 1) { // No need to evaluate the arguments, we just unify.
                      //We only solve the puzzle on arguments since there are no more variables
                      /** Returns an arrangment of variables v such that the goal is build only out of v's*/
                      def puzzle(v: Seq[Var], pieces: Seq[Exp], goal: Exp): Stream[Exp] = {
                        pieces.toStream.zip(v.toStream).collect[Exp, Stream[Exp]]{
                          case (piece, v) if piece == goal => v
                        } #::: (goal match {
                          case Application(a, Seq(b)) =>
                            for {va <- puzzle(v, pieces, a)
                                 vb <- puzzle(v, pieces, b) } yield {
                              Application(va, Seq(vb)): Exp
                            }
                          case _ =>
                            Stream.empty[Exp]
                        })
                      }
                      // Need to see if we can rearrange the arguments to produce the RHS.
                      for{ solution <- puzzle(argNames, arguments, out.exp) } yield {
                        in.assignmentsAsOriginals() combineWith Cont(v -> StrongValue(Lambda(argNames, solution)))
                      }
                    } else {
                      // s"We assign to everything else than $v their value")
                      // We try to evaluate everything else so that we only have unification to do.
                      val newArguments = arguments.map { arg =>
                        preMap{
                          case Application(Var(v), args2) if originalVariables contains v =>
                            in.context.partialAssignments.flatMap(assign => maybeEvalWithCache(assign._1(v))) match {
                              case Some(Lambda(nArg, nBody, nBuilder)) =>
                                Some(replaceFromVars(nArg.zip(args2).toMap, nBody))
                              case _ => None
                            }
                          case Var(v) if originalVariables contains v =>
                            in.context.partialAssignments.flatMap(assign => maybeEvalWithCache(assign._1(v)))
                          case _ => None
                        }(arg)
                      }
                      if(newArguments != arguments) {
                        for{ pf <- repair(in.subExpr(Application(v, newArguments)), out) } yield {
                          ContExp(in.exp, pf.context)
                        }
                      } else {
                        // s"Warning: We could not change the arguments $arguments")
                        Stream.empty
                      }
                    }
                  }

                  def modifyArguments: Stream[ContExp] = {
                    if (originalVariables.size >= 2) {
                      // "Modifying arguments:"
                      // Second we keep the original in.expr and try to modify the arguments
                      val updatedBody = replaceFromVars(argNames.zip(arguments).toMap, body)
                      for {pf <- repair(in.subExpr(updatedBody), out)} yield {
                        ContExp(in.exp, pf.context combineWith Cont(v -> OriginalValue(originalValue)))
                      }
                    } else Stream.empty
                  }

                  modifyFunction #::: modifyArguments
                case _ => Stream.empty
              }
              /*val originalValues = arguments.map(arg => maybeEvalWithCache(letm(currentValues) in arg).getOrElse{ throw new Exception(s"Could not evaluate $arg")})
              for{exception <- originalVariables

              }

              Stream( in.assignmentsAsOriginals() combineWith Cont(out.expr === in.expr) )*/
            }
          case None => // The lambda itself could not be evaluated.
            // We can only do something if the in.exp call is the same as the other one.
            out.exp match {
              case Application(v, args) if v == lambdaExpr =>
                // In this case, all the arguments have to be equal and we return only the context.
                for {
                  contexts <- inox.utils.StreamUtils.cartesianProduct(arguments.zip(args).map {
                    case (arg, newArg) =>
                      repair(in.subExpr(arg), out.subExpr(newArg)).map(_.context)
                  })
                  context = Cont(contexts)
                } yield {
                  ContExp(in.exp, context)
                }
            }
          case _ => Stream.empty // throw new Exception(s"Don't know how to handle this case : $originalValueMaybe of type ${originalValueMaybe.get.getClass.getName}")
        }
      case _ => Stream.empty
    }
  }
}
