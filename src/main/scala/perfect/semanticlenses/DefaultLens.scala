package perfect
package semanticlenses
import inox._
import inox.trees._
import inox.trees.dsl._
import ReverseProgram.Cache

/**
  * Created by Mikael on 05/05/2017.
  */

object DefaultLens extends SemanticLens {
  import ReverseProgram.repair
  import lenses.Lenses.StringConcatLens
  import Utils.ifEmpty
  import ReverseProgram.maybeEvalWithCache
  import StringConcatExtended._

  def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    in.expr match {
    // Literals without any free variables should be immediately replaced by the new value
    case l: Literal[_] => Stream(out)

    case fun@Lambda(vds, body) =>
      /** Replaces the vds by universally quantified variables */
      def unify: Stream[ProgramFormula] = {
        if(exprOps.variablesOf(fun).nonEmpty) {
          Utils.optVar(out.expr).flatMap(out.formula.findStrongConstraintValue).getOrElse(out.expr) match {
            case Lambda(vds2, body2) =>
              val freshVariables1 = vds.map(vd => Variable(FreshIdentifier(vd.id.name, true), vd.tpe, vd.flags))
              val freshBody1 = exprOps.replaceFromSymbols(vds.zip(freshVariables1).toMap, body)
              val freshBody2 = exprOps.replaceFromSymbols(vds2.zip(freshVariables1).toMap, body2)
              val universallyQuantified = Formula(freshVariables1.map(v => v -> AllValues).toMap)
              for{ pf <- repair(in.subExpr(freshBody1) combineWith universallyQuantified,
                out.subExpr(freshBody2) combineWith universallyQuantified) } yield {
                pf.wrap { newBody =>
                  val abstractedBody = exprOps.replaceFromSymbols(
                    freshVariables1.map(_.toVal).zip(vds.map(_.toVariable)).toMap, pf.expr)
                  Lambda(vds, abstractedBody)
                }
              }
            case _ => Stream.empty
          }
        } else {
          Stream.empty
        }
      }

      unify #::: Stream(out)

    // Variables are assigned the given value.
    case v: Variable =>
      Stream(ProgramFormula(v, out.formula combineWith Formula(v -> StrongValue(out.expr))))

    case Let(vd, expr, body) =>
      repair(ProgramFormula(Application(Lambda(Seq(vd), body), Seq(expr)), in.formula).wrappingDisabled, out).map {
        case ProgramFormula(Application(Lambda(Seq(vd), body), Seq(expr)), f) =>
          ProgramFormula(Let(vd, expr, body), f)
        case e  => throw new Exception(s"Don't know how to get a Let back from $e")
      }

    case Application(lambdaExpr, arguments) => // TODO: Put this into a lense.
      val originalValueMaybe: Option[Expr] = (Utils.optVar(lambdaExpr).flatMap(in.formula.findConstraintValue).getOrElse(lambdaExpr) match {
        /*case v: Variable =>
          currentValues.get(v).map(_.getValue).flatten.orElse(maybeEvalWithCache(functionFormula.assignments.get(v)))*/
        case l: Lambda => Some(l)
        //case _ => throw new Exception("Don't know how to deal with an application over non-lambda: "+lambdaExpr)
        case l => in.formula.partialAssignments.flatMap(assign => maybeEvalWithCache(assign._1(l)))
      }) // /: Log.Original_Value

      // Returns the new list of arguments plus a mapping from old to new values.
      def freshenArgsList(argNames: Seq[Variable]): (Seq[Variable], Map[Variable, Variable], Map[Variable, Variable]) = {
        val freshArgsNames = argNames.map(vd => Variable(FreshIdentifier(vd.id.name, true), vd.tpe, vd.flags))
        val oldToFresh = argNames.zip(freshArgsNames).toMap
        val freshToOld = freshArgsNames.zip(argNames).toMap
        (freshArgsNames, oldToFresh, freshToOld)
      }

      originalValueMaybe match {
        case Some(originalValue@Lambda(argNames, body)) =>
          val (freshArgsNames, oldToFresh, freshToOld) = freshenArgsList(argNames.map(_.toVariable))
          @inline def renew(e: Expr) = exprOps.replaceFromSymbols(oldToFresh, e)
          @inline def back(e: Expr) = exprOps.replaceFromSymbols(freshToOld, e)
          object Back { def unapply(e: KnownValue) = Some(e.map(back)) }

          val freshBody = renew(body)
          val assignments = in.formula.assignments
          val argumentVals =
            arguments.map( arg =>
              assignments.flatMap(assign => maybeEvalWithCache(assign(arg)).map(v => OriginalValue(v)))
            )

          if(argumentVals.forall(_.nonEmpty)) {
            val argumentValues = freshArgsNames.zip(argumentVals.map(_.get)).toMap
            val newpf = (in.subExpr(freshBody) combineWith Formula(argumentValues)).wrappingEnabled

            def backPf(newBodyFresh: Expr, newBodyFreshFormula: Formula): Expr = {
              val toInline = newBodyFreshFormula.known.collect{
                case (k, v@Back(newv)) if newv != v => k -> newv.getValue.get
              }
              exprOps.preMap({
                case v: Variable => toInline.get(v)
                case _ => None
              }, true)(back(newBodyFresh)) /: Log.prefix(s"backpf($newBodyFresh, $newBodyFreshFormula) = ")
            }

            for {pf <- repair(newpf, out)
                 ProgramFormula(newBodyFresh, newBodyFormula) = pf
                 newBody = backPf(newBodyFresh, newBodyFormula)
                 isSameBody = (newBody == body) /: Log.isSameBody
                 args <- ProgramFormula.regroupArguments(arguments.zip(freshArgsNames).map { case (arg, expected) =>
                     repair(in.subExpr(arg), out.subExpr(expected) combineWith newBodyFormula combineWith Formula(expected -> argumentValues(expected)))
                   })
                 (newArguments, newArgumentsFormula) = args
                 newLambda = if (isSameBody) originalValue else Lambda(argNames, newBody)
                 pfLambda <- lambdaExpr match {
                   case v: Variable => Stream(ProgramFormula(v, (
                     if (isSameBody) Formula() else
                       Formula(v -> StrongValue(newLambda)))))
                   case l => repair(ProgramFormula(l, in.formula),
                     out.subExpr(newLambda) combineWith newBodyFormula)
                 }
                 ProgramFormula(newAppliee, lambdaRepairFormula) = pfLambda
                 finalApplication = Application(newAppliee, newArguments) /: Log.prefix("finalApplication")
            } yield {
              Log(s"newBodyFormula: $newBodyFormula")
              Log(s"lambdaRepairFormula: $lambdaRepairFormula")
              Log(s"newArgumentsFormula: $newArgumentsFormula")
              val varsToRemove = freshArgsNames.filter{ v => !exprOps.exists{ case `v` => true case _ => false}(finalApplication)}
              val combinedFormula = newBodyFormula combineWith lambdaRepairFormula combineWith
                newArgumentsFormula removeArgs varsToRemove
              Log.prefix("[return] ") :=
                ProgramFormula(finalApplication: Expr, combinedFormula)
            }
          } else {
            // We can influcence only the variables's values which do not appear in output
            // We try to set up all known variables to their values except for one.
            val originalVariables = in.freeVars.filter(x => in.formula.findConstraintValue(x).nonEmpty)
            Log(s"Some argument values are not known. We only try unification. Variables = $originalVariables")
            // We try to evaluate the in.expr or evaluate all the arguments.
            lambdaExpr match {
              case v: Variable if (originalVariables contains v) &&
                !arguments.exists(arg => exprOps.exists{ case v2: Variable if v2 == v => true  case _ => false}(arg)) => // The variable should not be used in arguments.
                Log(s"The caller is a variable not used in arguments")
                def modifyFunction: Stream[ProgramFormula] = {
                  if (originalVariables.size == 1) { // No need to evaluate the arguments, we just unify.
                    Log("We only solve the puzzle on arguments since there are no more variables")
                    /** Returns an arrangment of variables v such that the goal is build only out of v's*/
                    def puzzle(v: Seq[ValDef], pieces: Seq[Expr], goal: Expr): Stream[Expr] = {
                      pieces.toStream.zip(v.toStream).collect[Expr, Stream[Expr]]{
                        case (piece, v) if piece == goal => v.toVariable
                      } #::: (goal match {
                        case Application(a, Seq(b)) =>
                          for {va <- puzzle(v, pieces, a)
                               vb <- puzzle(v, pieces, b) } yield {
                            Application(va, Seq(vb)): Expr
                          }
                        case _ =>
                          Stream.empty[Expr]
                      })
                    }
                    // Need to see if we can rearrange the arguments to produce the RHS.
                    for{ solution <- puzzle(argNames, arguments, out.expr) } yield {
                      in.assignmentsAsOriginals() combineWith Formula(v -> StrongValue(Lambda(argNames, solution)))
                    }
                  } else {
                    Log(s"We assign to everything else than $v their value")
                    // We try to evaluate everything else so that we only have unification to do.
                    val newArguments = arguments.map { arg =>
                      exprOps.preMap{
                        case Application(v: Variable, args2) if originalVariables contains v =>
                          in.formula.partialAssignments.flatMap(assign => maybeEvalWithCache(assign._1(v))) match {
                            case Some(Lambda(nArg, nBody)) =>
                              Some(exprOps.replaceFromSymbols(nArg.map(_.toVariable).zip(args2).toMap, nBody))
                            case _ => None
                          }
                        case v: Variable if originalVariables contains v =>
                          in.formula.partialAssignments.flatMap(assign => maybeEvalWithCache(assign._1(v)))
                        case _ => None
                      }(arg)
                    }
                    if(newArguments != arguments) {
                      for{ pf <- repair(in.subExpr(Application(v, newArguments)), out) } yield {
                        ProgramFormula(in.expr, pf.formula)
                      }
                    } else {
                      Log(s"Warning: We could not change the arguments $arguments")
                      Stream.empty
                    }
                  }
                }

                def modifyArguments: Stream[ProgramFormula] = {
                  if (originalVariables.size >= 2) {
                    Log("Modifying arguments:")
                    // Second we keep the original in.expr and try to modify the arguments
                    val updatedBody = exprOps.replaceFromSymbols(argNames.zip(arguments).toMap, body)
                    for {pf <- repair(in.subExpr(updatedBody), out)} yield {
                      ProgramFormula(in.expr, pf.formula combineWith Formula(v -> OriginalValue(originalValue)))
                    }
                  } else Stream.empty
                }

                modifyFunction #::: modifyArguments
              case _ => Stream.empty
            }
            /*val originalValues = arguments.map(arg => maybeEvalWithCache(letm(currentValues) in arg).getOrElse{ throw new Exception(s"Could not evaluate $arg")})
            for{exception <- originalVariables

            }

            Stream( in.assignmentsAsOriginals() combineWith Formula(out.expr === in.expr) )*/
          }
        case None =>
          // We can only do something if the in.expr call is the same as the other one.
          out.expr match {
            case Application(v, args) if v == lambdaExpr =>
              // In this case, all the arguments have to be equal and we return only the formula.
              for {
                formulas <- inox.utils.StreamUtils.cartesianProduct(arguments.zip(args).map {
                  case (arg, newArg) =>
                    repair(in.subExpr(arg), out.subExpr(newArg)).map(_.formula)
                })
                formula = Formula(formulas)
              } yield {
                ProgramFormula(in.expr, formula)
              }
          }
        case _ => throw new Exception(s"Don't know how to handle this case : $originalValueMaybe of type ${originalValueMaybe.get.getClass.getName}")
      }

    case IfExpr(cond, thenn, elze) =>
      val cond_v = in.formula.assignments.flatMap(assign => maybeEvalWithCache(assign(cond))).getOrElse(return Stream.Empty)
      cond_v match {
        case BooleanLiteral(true) =>
          for(pf <- repair(in.subExpr(thenn), out)) yield
            pf.wrap(x => IfExpr(cond, x, elze))
        case BooleanLiteral(false) =>
          for(pf <- repair(in.subExpr(elze), out)) yield
            pf.wrap(x => IfExpr(cond, thenn, x))
        case _ => throw new Exception(s"Not a boolean: $cond_v")
      }
    case AsInstanceOf(a, tpe) =>
      for{ p <- repair(in.subExpr(a), out)} yield p.wrap(x => AsInstanceOf(x, tpe) )
    case anyExpr =>
      Log(s"[Warning] Don't know how to handle this case : $anyExpr of type ${anyExpr.getClass.getName},\nIt evaluates to:\n${in.getFunctionValue}.")
      Stream(out)
    }
  }
}