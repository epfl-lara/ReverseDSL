package perfect

import inox.Identifier
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import perfect.semanticlenses._

import scala.collection.mutable.{HashMap, ListBuffer}

/**
  * Created by Mikael on 03/03/2017.
  */
object ReverseProgram extends lenses.Lenses {
  import StringConcatExtended._
  type FunctionEntry = Identifier
  type ModificationSteps = Unit
  type OutExpr = Expr
  type Cache = HashMap[Expr, Expr]

  import Utils._
  import InoxConvertible._
  lazy val context = Context.empty.copy(options = Options(Seq(optSelectedSolvers(Set("smt-cvc4")))))

  import Utils.ifEmpty

  /** Main entry point to reverse a program.
    * @param outProg The output that the program should produce
    * @param prevIn The program to repair. May be empty, in which case it returns outProg
    * @return The program prevIn such that it locally produces the changes given by outProg */
  def put(outProg: ProgramFormula, prevIn: Option[Expr]): Stream[Expr] = {
    if(prevIn == None) {
      val outExpr = outProg.bodyDefinition.getOrElse(throw new Exception(s"Ill-formed program: $outProg"))
      return Stream(outExpr)
    }

    implicit val symbols = defaultSymbols.withFunctions(ReverseProgram.funDefs)
    implicit val cache = new Cache
    for { r <- repair(ProgramFormula(prevIn.get), outProg)
          ProgramFormula(newOutExpr, f) = r.insertVariables()                    /: Log.remaining_program
          assignments <- f.determinizeAll(exprOps.variablesOf(newOutExpr).toSeq) /:: Log.found_assignments
          finalNewOutExpr = exprOps.replaceFromSymbols(assignments, newOutExpr)  /: Log.final_expression
    } yield finalNewOutExpr
  }

  /** Alternative way of reversing a program.
    * @param outProg The output that the program should produce
    * @param prevIn The program to repair, along with assignment formulas. May be empty, in which case it returns outProg
    * @return The program prevIn such that it locally produces the changes given by outProg */
  def put(outProg: ProgramFormula, prevIn: ProgramFormula): Stream[ProgramFormula] = {
    implicit val symbols = defaultSymbols.withFunctions(ReverseProgram.funDefs)
    implicit val cache = new Cache
    for { r <- repair(prevIn, outProg) } yield r.insertVariables() /: Log.remaining_program
  }
    /** Reverses a parameterless function, if possible.*/
  def putPf(outProg: ProgramFormula, prevIn: Option[(InoxProgram, FunctionEntry)]): Iterable[(InoxProgram, FunctionEntry)] = {
    val newMain = FreshIdentifier("main")
    put(outProg, prevIn.map{ case (prevProgram, prevFunctionEntry) =>
      val prevFunction = prevProgram.symbols.functions.getOrElse(prevFunctionEntry, return Nil)
      prevFunction.fullBody
    }).map{ finalNewOutExpr =>
      implicit val symbols = prevIn.map(_._1.symbols).getOrElse(defaultSymbols)
      val newFunDef = mkFunDef(newMain)()(stp => (Seq(), finalNewOutExpr.getType, _ => finalNewOutExpr))
      val newProgram = InoxProgram(context, symbols.withFunctions(newFunDef::ReverseProgram.funDefs))
      (newProgram, newMain)
    }
    /*
    if(prevIn == None) {
      implicit val symbols = defaultSymbols
      val main = FreshIdentifier("main")
      val fundef = mkFunDef(main)()(stp => (Seq(), outExpr.getType, _ => outExpr))
      return Stream((InoxProgram(context, Seq(fundef), allConstructors), main))
    }
    val (prevProgram, prevFunctionEntry) = prevIn.get
    implicit val symbols = prevProgram.symbols

    val newMain = FreshIdentifier("main")
    implicit val cache = new HashMap[Expr, Expr]
    for { r <- repair(ProgramFormula(prevBody), outProg)
         ProgramFormula(newOutExpr, f) = r
         _ = Log("Remaining formula: " + f)
         _ = Log("Remaining expression: " + newOutExpr)
         assignments <- f.determinizeAll(exprOps.variablesOf(newOutExpr).toSeq.map(_.toVal))
         _ = Log("Found assignments: " + assignments)
         finalNewOutExpr = exprOps.replaceFromSymbols(assignments, newOutExpr)
         _ = Log("Final  expression: " + finalNewOutExpr)
         newFunDef = mkFunDef(newMain)()(stp => (Seq(), prevFunction.returnType, _ => finalNewOutExpr))
         newProgram = InoxProgram(context, symbols.withFunctions(Seq(newFunDef)))
    } yield (newProgram, newMain)*/
  }

  def simplify(expr: Expr)(implicit cache: Cache, symbols: Symbols): Expr = {
    if(exprOps.variablesOf(expr).isEmpty) {
      evalWithCache(expr)
    } else expr
  }

  /** Eval function. Uses a cache normally. Does not evaluate already evaluated expressions. */
  def evalWithCache(expr: Expr)(implicit cache: Cache, symbols: Symbols) = cache.getOrElseUpdate(expr, {
    expr match {
      case l:Lambda => expr
      case _ =>
        import evaluators._
        val p = InoxProgram(context, symbols)
        val evaluator = LambdaPreservingEvaluator(p)
        evaluator.eval(expr) match {
          case EvaluationResults.Successful(e) => e
          case m => throw new Exception(s"Could not evaluate: $expr, got $m")
        }
    }
  })

  def maybeEvalWithCache(expr: Expr)(implicit cache: Cache, symbols: Symbols): Option[Expr] = {
    if(cache.contains(expr)) {
      Some(cache(expr))
    } else {
      import evaluators._
      val p = InoxProgram(context, symbols)
      val evaluator = LambdaPreservingEvaluator(p)
      evaluator.eval(expr) match {
        case EvaluationResults.Successful(e) =>
          cache(expr) = e
          Some(e)
        case m => Log(s"Could not evaluate: $expr, got $m")
          None
      }
    }
  }


  /** Returns an evaluator which preserves lambda shapes */
  def LambdaPreservingEvaluator(p: InoxProgram) = {
    import evaluators._
    new {
      val program: p.type = p
      val options = context.options
    } with LambdaPreservingEvaluator
      with HasDefaultGlobalContext with HasDefaultRecContext {
      val semantics: p.Semantics = p.getSemantics
    }
  }

  /** Applies the interleaving to a finite sequence of streams. */
  def interleave[T](left: Stream[T])(right: => Stream[T]) : Stream[T] = {
    if (left.isEmpty) right else left.head #:: interleave(right)(left.tail)
  }

  val semanticLenses: semanticlenses.SemanticLens =
    PatternMatch.Lens andThen
      PatternReplace.Lens andThen
      ListInsert.Lens andThen
      PasteVariable.Lens andThen
      StringInsert.Lens andThen
      perfect.lenses.SetLens andThen
      perfect.lenses.MapDataLens

  /** Will try its best to transform prevOutExpr so that it produces newOut or at least incorporates the changes.
    * Basically, we solve the problem:
    *  let variables = values in function = newOut
    * by trying to change the variables values, or the function body itself.
    *
    * @param program An expression that computed the value before newOut, and the formula contains the current mappings.
    * @param newOutProgram A ProgramFormula resulting from the action of the user on the datat.
    *               Either a literal value that should be produced by function,
    *               or a variable, in which case the result will have in the formula a constraint over this variable,
    *               Or an expression with constrained free variables to denote a clone-and-paste or many other things.
    * @return A set of possible expressions, along with a set of possible assignments to input variables.
    **/
  def repair(program: ProgramFormula, newOutProgram: ProgramFormula)
            (implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    val ProgramFormula(function, functionFormula) = program
    val ProgramFormula(newOut, newOutFormula) = newOutProgram
    val currentValues = functionFormula.known
    val stackLevel = Thread.currentThread().getStackTrace.length
    Log(s"\n@repair$stackLevel(\n  $program\n, $newOutProgram)")
    if(function == newOut) return { Log("@return original without constraints");
      Stream(program.assignmentsAsOriginals())
    }

    val newOutBestValue = newOutProgram.simplifiedExpr
    
    // Accelerators without evaluating the function
    newOutBestValue match {
      case ProgramFormula.TreeWrap.Expr(original, wrapper) if program.canDoWrapping =>
        function match {
          case l: Let =>
          case Application(Lambda(_, _), _) =>
          case _ =>
            return Stream(ProgramFormula(wrapper(function)))
        }
      case ProgramFormula.TreeUnwrap.Expr(tpe, original, Nil) =>
        return Stream(program.assignmentsAsOriginals())
      case ProgramFormula.TreeUnwrap.Expr(tpe, original, head::tail) =>
        function match {
          case l@ADT(ADTType(adtid, tps), args) =>
            symbols.adts(adtid) match {
              case f: ADTConstructor =>
                val i = f.selectorID2Index(head)
                return repair(program.subExpr(args(i)), ProgramFormula.TreeUnwrap(tpe, args(i), tail))
              case _ =>
            }
          case _ =>
        }
      case ProgramFormula.TreeModification.Expr(tpeG, tpeL, _, modified, Nil) =>
        return repair(program, newOutProgram.subExpr(modified))
      case ProgramFormula.TreeModification.Expr(tpeG, tpeL, original, modified, head::tail) =>
        function match {
          case l@ADT(ADTType(adtid, tps), args) =>
            symbols.adts(adtid) match {
              case f: ADTConstructor =>
                val i = f.selectorID2Index(head)
                original match {
                  case ADT(_, argsOriginal) =>
                    val subOriginal = argsOriginal(i)
                    return for{ pf <- repair(program.subExpr(args(i)),
                      ProgramFormula.TreeModification(subOriginal.getType, tpeL, subOriginal, modified, tail)) } yield {
                      pf.wrap(x =>
                        ADT(l.adt, args.take(i) ++ List(x) ++ args.drop(i + 1)))
                    }
                }
              case _ =>
            }
          case _ =>
        }
      case _ =>
    }

    lazy val functionValue: Option[Expr] = program.getFunctionValue

    if(!newOut.isInstanceOf[Variable] &&
      functionValue.nonEmpty && !functionValue.get.isInstanceOf[FiniteMap]
       && functionValue.get == newOut) return {
      Log("@return original function");
      Stream(program.assignmentsAsOriginals() combineWith newOutFormula)
    }
    //Log(s"functionValue ($functionValue) != newOut ($newOut)")

    //Log.prefix(s"@return ") :=
    def maybeWrappedSolutions = if(functionValue.isEmpty) Stream.empty else (function.getType match {
        case a: ADTType if !newOut.isInstanceOf[Variable] =>
          function match {
            case l: Let => Stream.empty[ProgramFormula] // No need to wrap a let expression, we can always do this later. Indeed,
              //f{val x = A; B} = {val x = A; f(B)}
            case Application(Lambda(_, _), _) => Stream.empty[ProgramFormula] // Same argument
            case _ if ListInsert.unapply(newOutProgram).nonEmpty => Stream.empty[ProgramFormula]
            case _ =>
              (maybeWrap(program, newOutProgram, functionValue.get) /:: Log.maybe_wrap) #::: (maybeUnwrap(program, newOutProgram, functionValue.get) /:: Log.maybe_unwrap)
          }
        case StringType if !newOut.isInstanceOf[Variable] && program.canDoWrapping =>
          function match {
            case l: Let => Stream.empty[ProgramFormula]
            case Application(Lambda(_, _), _) => Stream.empty[ProgramFormula]
            case _ =>
              // Stream.empty
              // Can be a StringConcat with constants to add or to remove.
              maybeWrapString(program, newOut, functionValue.get)// #::: maybeUnwrapString(program, newOut, functionValue)
          }
        case _ => Stream.empty[ProgramFormula]
      })

    def originalSolutions : Stream[ProgramFormula] = {
      function match {
        // Values (including lambdas) should be immediately replaced by the new value
        case l: Literal[_] => Stream(newOutProgram)

        case fun@Lambda(vds, body) =>

          /** Replaces the vds by universally quantified variables */
          def unify: Stream[ProgramFormula] = {
            if(exprOps.variablesOf(fun).nonEmpty) {
              optVar(newOut).flatMap(newOutFormula.findStrongConstraintValue).getOrElse(newOut) match {
                case Lambda(vds2, body2) =>
                  val freshVariables1 = vds.map(vd => Variable(FreshIdentifier(vd.id.name, true), vd.tpe, vd.flags))
                  val freshBody1 = exprOps.replaceFromSymbols(vds.zip(freshVariables1).toMap, body)
                  val freshBody2 = exprOps.replaceFromSymbols(vds2.zip(freshVariables1).toMap, body2)
                  val universallyQuantified = Formula(freshVariables1.map(v => v -> AllValues).toMap)
                  for{ pf <- repair(program.subExpr(freshBody1) combineWith universallyQuantified,
                    newOutProgram.subExpr(freshBody2) combineWith universallyQuantified) } yield {
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

          unify #::: Stream(newOutProgram)

        // Variables are assigned the given value.
        case v@Variable(id, tpe, flags) =>
          Stream(ProgramFormula(v, Formula(v -> StrongValue(newOut)) combineWith newOutFormula))

        case Let(vd, expr, body) =>
          repair(ProgramFormula(Application(Lambda(Seq(vd), body), Seq(expr)), program.formula),
            newOutProgram).map {
            case ProgramFormula(Application(Lambda(Seq(vd), body), Seq(expr)), f) =>
              ProgramFormula(Let(vd, expr, body), f)
            case e  => throw new Exception(s"Don't know how to get a Let back from $e")
          }

        case StringConcat(expr1, expr2) =>
          val pf = newOutProgram
          val replacement = program.subExpr(FunctionInvocation(StringConcatLens.identifier, Nil,
            Seq(expr1, expr2)))
          val replacementOut = newOutProgram.wrap{
            case StringConcat(a, b) =>
              FunctionInvocation(StringConcatLens.identifier, Nil, Seq(a, b))
            case e => e
          }

          ifEmpty(for (pf <- repair(replacement, replacementOut)) yield {
            pf match {
              case ProgramFormula(FunctionInvocation(StringConcatLens.identifier, Nil, Seq(x, y)), f) =>
                ProgramFormula(StringConcat(x, y), f)
            }
          }) {
            val constraint = newOut === function // We want to avoid at maximum having to solve constraints.
            Stream(ProgramFormula(function, Formula(Map(), constraint)))
          } #::: {
            // Handle insertion between two non-constants as a possible constant at the last resort.
            newOutProgram match {
              case StringInsert(left, inserted, right, direction)
                if !expr1.isInstanceOf[StringLiteral] && !expr2.isInstanceOf[StringLiteral] &&
                  maybeEvalWithCache(functionFormula.assignments.get(expr1)) == Some(StringLiteral(left)) &&
                  maybeEvalWithCache(functionFormula.assignments.get(expr2)) == Some(StringLiteral(right))
              => Stream(program.subExpr(expr1 +& StringLiteral(inserted) +& expr2).assignmentsAsOriginals())
              case _ => Stream.empty[ProgramFormula]
            }
          }

        case ADT(adtType@ADTType(tp, tpArgs), argsIn) =>
          newOutBestValue match {
            case ADT(ADTType(tp2, tpArgs2), argsOut) if tp2 == tp && tpArgs2 == tpArgs && functionValue != Some(newOut) => // Same type ! Maybe the arguments will change or move.
              Log("ADT 2")
              val argsInValue = functionValue match {
                case Some(ADT(ADTType(_, _), argsInValue)) => argsInValue.map(x => Some(x))
                case _ => argsIn.map(_ => None)
              }

              val seqOfStreamSolutions = (argsIn.zip(argsInValue)).zip(argsOut).map { case ((aFun, aFunVal), newOutArg) =>
                repair(ProgramFormula(aFun, program.formula).withComputedValue(aFunVal), newOutProgram.subExpr(newOutArg))
              }
              val streamOfSeqSolutions = inox.utils.StreamUtils.cartesianProduct(seqOfStreamSolutions)
              for {seq <- streamOfSeqSolutions
                   _ = Log(s"combineResults($seq)")
                   (newArgs, assignments) = ProgramFormula.combineResults(seq)
              } yield {
                ProgramFormula(ADT(ADTType(tp2, tpArgs2), newArgs), assignments)
              }
            case _: Variable =>
              Stream(newOutProgram)
            case ADT(ADTType(_, _), _) =>
              Stream.empty // Wrapping already handled.

            case a =>
              Log(s"[Warning] Don't know how to handle this case : $a is supposed to be put in place of a ${tp}")
              Stream.empty
          }

        case as@ADTSelector(adt, selector) =>
          val originalAdtValue = evalWithCache(functionFormula.assignments.get(adt)).asInstanceOf[ADT]
          val constructor = as.constructor.get
          val fields = constructor.fields
          val index = as.selectorIndex
          val vrs = fields.map{ fd => Variable(FreshIdentifier("x", true), fd.getType, Set())}
          val constraints = vrs.zipWithIndex.map{
            case (vd, i) => vd -> (if(i == index) StrongValue(newOut) else OriginalValue(originalAdtValue.args(i)))
          }.toMap
          val newConstraint = Formula(constraints)

          for{ pf <- repair(program.subExpr(adt),
            newOutProgram.subExpr(ADT(ADTType(constructor.id, constructor.tps), vrs)) combineWith newConstraint) } yield {
            pf.wrap(x => ADTSelector(x, selector))
          }

        case Application(lambdaExpr, arguments) => // TODO: Put this into a lense.
          val originalValueMaybe: Option[Expr] = (optVar(lambdaExpr).flatMap(functionFormula.findConstraintValue).getOrElse(lambdaExpr) match {
            /*case v: Variable =>
              currentValues.get(v).map(_.getValue).flatten.orElse(maybeEvalWithCache(functionFormula.assignments.get(v)))*/
            case l: Lambda => Some(l)
            //case _ => throw new Exception("Don't know how to deal with an application over non-lambda: "+lambdaExpr)
            case l => functionFormula.partialAssignments.flatMap(assign => maybeEvalWithCache(assign._1(l)))
          }) /: Log.Original_Value

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

              val freshBody = renew(body)
              val assignments = functionFormula.assignments
              val argumentVals =
                arguments.map( arg =>
                  assignments.flatMap(assign => maybeEvalWithCache(assign(arg)).map(v => OriginalValue(v)))
                )

              if(argumentVals.forall(_.nonEmpty)) {
                val argumentValues = freshArgsNames.zip(argumentVals.map(_.get)).toMap
                val newpf = (program.subExpr(freshBody) combineWith Formula(argumentValues)).wrappingEnabled

                def backPf(newBodyFresh: Expr, newBodyFreshFormula: Formula): (Expr, Formula) = {
                  val (newKnown, toInline) = ((Map[Variable, KnownValue](), Map[Variable, Expr]()) /: newBodyFreshFormula.known) {
                    case ((newKnown, toInline), (k, v)) =>
                      val newv = v.map(back)
                      if(newv != v) { // A value changed, it means that it contained the old variable, so we need to inline this value.
                        (newKnown, toInline + (k -> back(v.getValue.get)))
                      } else {
                        (newKnown + (k -> newv), toInline)
                      }
                  }
                  val newBody =
                    exprOps.preMap({
                      case v: Variable => toInline.get(v)
                      case _ => None
                    }, true)(back(newBodyFresh))
                  (newBody, Formula(newKnown, newBodyFreshFormula.constraints)) /: Log.prefix(s"backpf($newBodyFresh, $newBodyFreshFormula) = ")
                }

                for {pf <- repair(newpf, newOutProgram) /:: Log.prefix(s"For repair$stackLevel, recovered:\n")
                     ProgramFormula(newBodyFresh, newBodyFreshFormula) = pf
                     (newBody, newBodyFormula) = backPf(newBodyFresh, newBodyFreshFormula)
                     isSameBody = (newBody == body) /: Log.isSameBody
                     args <-
                     ProgramFormula.combineArguments(program,
                       arguments.zip(freshArgsNames).map { case (arg, expected) =>
                         (arg, newOutProgram.subExpr(expected) combineWith newBodyFormula combineWith Formula(expected -> argumentValues(expected)))
                       })
                     (newArguments, newArgumentsFormula) = args
                     newLambda = if (isSameBody) originalValue else Lambda(argNames, newBody)
                     pfLambda <- lambdaExpr match {
                       case v: Variable => Stream(ProgramFormula(v, (
                         if (isSameBody) Formula() else
                           Formula(v -> StrongValue(newLambda)))))
                       case l => repair(ProgramFormula(l, program.formula),
                         newOutProgram.subExpr(newLambda) combineWith newBodyFormula)
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
                val originalVariables = program.freeVars.filter(x => program.formula.findConstraintValue(x).nonEmpty)
                Log(s"Some argument values are not known. We only try unification. Variables = $originalVariables")
                // We try to evaluate the function or evaluate all the arguments.
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
                        for{ solution <- puzzle(argNames, arguments, newOut) } yield {
                          program.assignmentsAsOriginals() combineWith Formula(v -> StrongValue(Lambda(argNames, solution)))
                        }
                      } else {
                        Log(s"We assign to everything else than $v their value")
                        // We try to evaluate everything else so that we only have unification to do.
                        val newArguments = arguments.map { arg =>
                          exprOps.preMap{
                            case Application(v: Variable, args2) if originalVariables contains v =>
                              functionFormula.partialAssignments.flatMap(assign => maybeEvalWithCache(assign._1(v))) match {
                                case Some(Lambda(nArg, nBody)) =>
                                  Some(exprOps.replaceFromSymbols(nArg.map(_.toVariable).zip(args2).toMap, nBody))
                                case _ => None
                              }
                            case v: Variable if originalVariables contains v =>
                              functionFormula.partialAssignments.flatMap(assign => maybeEvalWithCache(assign._1(v)))
                            case _ => None
                          }(arg)
                        }
                        if(newArguments != arguments) {
                          for{ pf <- repair(program.subExpr(Application(v, newArguments)), newOutProgram) } yield {
                            ProgramFormula(function, pf.formula)
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
                        // Second we keep the original function and try to modify the arguments
                        val updatedBody = exprOps.replaceFromSymbols(argNames.zip(arguments).toMap, body)
                        for {pf <- repair(program.subExpr(updatedBody), newOutProgram)} yield {
                          ProgramFormula(function, pf.formula combineWith Formula(v -> OriginalValue(originalValue)))
                        }
                      } else Stream.empty
                    }

                    modifyFunction #::: modifyArguments
                  case _ => Stream.empty
                }
                /*val originalValues = arguments.map(arg => maybeEvalWithCache(letm(currentValues) in arg).getOrElse{ throw new Exception(s"Could not evaluate $arg")})
                for{exception <- originalVariables

                }

                Stream( program.assignmentsAsOriginals() combineWith Formula(newOutProgram.expr === program.expr) )*/
              }
            case None =>
              // We can only do something if the function call is the same as the other one.
              newOut match {
                case Application(v, args) if v == lambdaExpr =>
                  // In this case, all the arguments have to be equal and we return only the formula.
                  for {
                    formulas <- inox.utils.StreamUtils.cartesianProduct(arguments.zip(args).map {
                      case (arg, newArg) =>
                        repair(program.subExpr(arg), newOutProgram.subExpr(newArg)).map(_.formula)
                    })
                    formula = Formula(formulas)
                  } yield {
                    ProgramFormula(function, formula)
                  }
              }
            case _ => throw new Exception(s"Don't know how to handle this case : $originalValueMaybe of type ${originalValueMaybe.get.getClass.getName}")
          }

        case funInv@FunctionInvocation(f, tpes, args) =>
          // We need to reverse the invocation arguments.
          reversions.get(f) match {
            case None => Stream.empty  /: Log.prefix(s"No function $f reversible for : $funInv.\nIt evaluates to:\n$functionValue.")
            case Some(lens) =>
              val assignments = functionFormula.partialAssignments.map(_._1)
              val argsOptValue = args.map(arg => assignments.flatMap(assign => maybeEvalWithCache(assign(arg)).map(program.subExpr)))
              if(argsOptValue.forall(_.nonEmpty)) {
                val lenseResult = lens.put(tpes)(argsOptValue.map(_.get), newOutProgram)
                for {l <- lenseResult; (newArgsValues, newForm) = l
                     a <- ProgramFormula.combineArguments(program, args.zip(newArgsValues))
                     (newArguments, newArgumentsFormula) = a
                } yield {
                  val formula = newForm combineWith newArgumentsFormula
                  ProgramFormula(FunctionInvocation(f, tpes, newArguments), formula)
                }
              } else { // There are universally quantified variables.
                newOut match {
                  case FunctionInvocation(`f`, tpes2, args2) if tpes2 == tpes =>
                    // There must be equivalence between arguments. Unification.
                    val argsRepaired = args.zip(args2) map {
                      case (a1, a2) => repair(program.subExpr(a1), newOutProgram.subExpr(a2))
                    }
                    for{psf <- ProgramFormula.regroupArguments(argsRepaired)
                        (ps, formula) = psf} yield {
                      ProgramFormula(FunctionInvocation(`f`, tpes, ps), formula)
                    }

                  case _ =>
                    Log("Warning: impossible to merge")
                    Stream.empty
                }
              }
          }

        // Special case where we prefer the cons-branch. For that we need to modify the input.
        /*case IfExpr(IsInstanceOf(v:Variable, ADTType(Utils.cons, Seq(tpe))), thenn, elze) =>
          val value_v = evalWithCache(letm(currentValues) in v)
          value_v match {
            case ListLiteral(List(), tpe) => // Let's try to complete the nil to something else so that it passes the thenn branch.
              val hd = Variable("hd", tpe, Set())
              val tl = Variable("tl", ADTType(Utils.list, Seq(tpe)), Set())
              val new_value_v = ListLiteral()

              repair(program.subExpr(thenn), newOutProgram)

              val newFormula = v === ADT(ADTType(Utils.cons, Seq(tpe)), Seq(hd, tl))

            case ListLiteral(_, _) => // Then-branch
              for(pf <- repair(program.subExpr(thenn), newOutProgram)) yield
                pf.wrap(x => IfExpr(cond, x, elze))
          }*/


        case IfExpr(cond, thenn, elze) =>
          val cond_v = evalWithCache(functionFormula.assignments.get(cond))
          cond_v match {
            case BooleanLiteral(true) =>
              for(pf <- repair(program.subExpr(thenn), newOutProgram)) yield
                pf.wrap(x => IfExpr(cond, x, elze))
            case BooleanLiteral(false) =>
              for(pf <- repair(program.subExpr(elze), newOutProgram)) yield
                pf.wrap(x => IfExpr(cond, thenn, x))
            case _ => throw new Exception(s"Not a boolean: $cond_v")
          }
        case AsInstanceOf(a, tpe) =>
          for{ p <- repair(program.subExpr(a), newOutProgram)} yield p.wrap(x => AsInstanceOf(x, tpe) )
        case anyExpr =>
          Log(s"Don't know how to handle this case : $anyExpr of type ${anyExpr.getClass.getName},\nIt evaluates to:\n$functionValue.")
          Stream.empty
      }
    }

    val originalLens = new SemanticLens {
      override def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
        originalSolutions
      }
    }

    (if(program.isWrappingLowPriority) {
      interleave { (semanticLenses andThen originalLens).put(program, newOutProgram) } { maybeWrappedSolutions }
    } else {
      interleave { maybeWrappedSolutions } { (semanticLenses andThen originalLens).put(program, newOutProgram) }
    }) #::: {
//      ???
      Log(s"Finished repair$stackLevel"); Stream.empty[ProgramFormula]}  /:: Log.prefix(s"@return for repair$stackLevel(\n  $program\n, $newOutProgram):\n~>")
  }

  /* Example:
    function = v
    functionValue = Element("b", List(), List(), List())
    newOut = Element("div", List(Element("b", List(), List(), List())), List(), List())
    result: Element("div", List(v), List(), List())
  * */
  private def maybeWrap(program: ProgramFormula, newOutProgram: ProgramFormula, functionValue: Expr)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    Log(s"Testing maybewrap for function Value = $functionValue")
    val newOut = newOutProgram.getFunctionValue.getOrElse(return Stream.empty)
    val function = program.expr
    if(functionValue == newOut) return Stream.empty[ProgramFormula] // Value returned in maybeUnwrap
    Log(s"maybewrap 2")

    val containsFunctionValue = exprOps.exists {
      case t if t == functionValue => true
      case _ => false
    } _
    // Checks if the old value is inside the new value, in which case we add a wrapper.
    if (containsFunctionValue(newOut)) {
      Log(s"maybewrap 3")
      val canWrap = newOut match {
        case ADT(ADTType(name, tps), args) =>
          function match {
            case ADT(ADTType(nameFun, tpsFun), argsFun) =>
              if(name != nameFun || tps != tpsFun) {
                true
              } else { // There might be a duplicate wrapping.
                val argsWithIndex = args.zipWithIndex
                val indexes = argsWithIndex.filter{ case (arg, i) =>
                  containsFunctionValue(arg)
                }
                if(indexes.length >= 2) {
                  true
                } else if(indexes.isEmpty) { // That's weird, should not happen.
                  Log("##### Error: This cannot happen #####")
                  false
                } else {
                  val (arg, i) = indexes.head
                  val shouldNotWrap = argsFun.zipWithIndex.forall{ case (arg2, i2) =>
                    println(s"Testing if $arg2 is value: ${isValue(arg2)}")
                    i2 == i || isValue(arg2)
                  }
                  /*if(shouldNotWrap) {
                    println("~~~~~~~~~~ Did not wrap this ~~~~~~~~")
                    println("  " + function)
                    println(" =" + functionValue)
                    println("->" + newOut)
                    println(s"because we would have the same wrapping at index $i")
                  }*/
                  !shouldNotWrap
                }
              }
            case _ => true
          }
        case _ => true
      }
      Log(s"canwrap: $canWrap")
      if(canWrap) {
        // We wrap the computation of functionValue with ADT construction
        val newFunction = exprOps.postMap {
          case t if t == functionValue => Some(function)
          case _ => None
        }(newOut)
        Stream(ProgramFormula(newFunction))
      } else Stream.empty
    } else {
      Stream.empty
    }
  }


  /* Example:
  *  function:      Element("b", List(v, Element("span", List(), List(), List())), List(), List())
  *  functionValue: Element("b", List(Element("span", List(), List(), List()), Element("span", List(), List(), List())), List(), List())
  *  newOut:        Element("span", List(), List(), List())
  *  result:        v  #::   Element("span", List(), List(), List()) #:: Stream.empty
  * */
  private def maybeUnwrap(program: ProgramFormula, newOutProgram: ProgramFormula, functionValue: Expr)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    val newOut = newOutProgram.getFunctionValue.getOrElse(return Stream.empty)
    val function = program.expr
    if(functionValue == newOut) {
      Log("@return unwrapped")
      return Stream(program.assignmentsAsOriginals())
    }

    (function, functionValue) match {
      case (ADT(ADTType(tp, tpArgs), args), ADT(ADTType(tp2, tpArgs2), argsValue)) =>
        // Checks if the old value is inside the new value, in which case we add a wrapper.
        argsValue.toStream.zipWithIndex.filter{ case (arg, i) =>
          exprOps.exists {
            case t if t == newOut => true
            case _ => false
          }(arg)
        }.flatMap{ case (arg, i) =>
          maybeUnwrap(ProgramFormula(args(i), program.formula), newOutProgram, arg)
        }

      case _ => Stream.empty
    }
  }

  /* Example:
    function = f(a) + v + "boss"
    functionValue = "I am the boss"
    newOut =  "Therefore, I am the boss"
    result: "Therefore, " + (f(a) + v + "boss")
  * */
  private def maybeWrapString(program: ProgramFormula, newOut: Expr, functionValue: Expr)(implicit symbols: Symbols): Stream[ProgramFormula] = {
    val function = program.expr
    if(functionValue == newOut) {
      Log("@return unwrapped")
      return Stream(program.assignmentsAsOriginals())
    }
    val StringLiteral(t) = functionValue

    object StringConcats {
      def unapply(e: Expr): Some[List[Expr]] = e match {
        case StringConcat(a, b) => Some(unapply(a).get ++ unapply(b).get)
        case e => Some(List(e))
      }
    }

    def wrapToRight(s: String) = {
      val StringConcats(atoms) = function
      if(atoms.lastOption.exists(x => x.isInstanceOf[StringLiteral])) { // We don't wrap in a new string if the last concatenation is a StringLiteral
        Stream.empty
      } else {
        Stream(ProgramFormula(StringConcat(function, StringLiteral(s))))
      }
    }

    def wrapToLeft(s: String) = {
      val StringConcats(atoms) = function
      if(atoms.headOption.exists(x => x.isInstanceOf[StringLiteral])) { // We don't wrap in a new string if the last concatenation is a StringLiteral
        Stream.empty
      } else {
        Stream(ProgramFormula(StringConcat(StringLiteral(s), function)))
      }
    }

    newOut match {
      case StringLiteral(s) =>
        function match {
          case StringLiteral(_) => Stream.empty // We can always replace the StringLiteral later
          case _ => (
            (if(s.startsWith(t)) wrapToRight(s.substring(t.length)) else Stream.empty) #:::
            (if(s.endsWith(t)) wrapToLeft(s.substring(0, s.length - t.length)) else Stream.empty)
            ) /:: Log.prefix("@return wrapped: ")
        }
      case StringInsert.Expr("", inserted, right, direction) if t == right => wrapToLeft(inserted)
      case StringInsert.Expr(left, inserted, "", direction) if t == left => wrapToRight(inserted)
      case _ => Stream.empty
    }
  }

  /* Example:
    function = "Therefore, " + f(a) + v + "boss"
    functionValue = "Therefore, I am the boss"
    newOut =  "I am the boss"
    result: f(a) + v + "boss" (we remove the empty string)
  * */
  /*private def maybeUnwrapString(program: ProgramFormula, newOut: Expr, functionValue: Expr)(implicit symbols: Symbols): Stream[ProgramFormula] = {
    val function = program.program
    if(functionValue == newOut) return Stream.empty

    def dropRightIfPossible(lReverse: List[Expr], toRemoveRight: String): Option[List[Expr]] =
      if(toRemoveRight == "") Some(lReverse.reverse) else lReverse match {
      case Nil => None
      case StringLiteral(last) :: lReverseTail =>
        if(toRemoveRight.endsWith(last))
          dropRightIfPossible(lReverseTail, toRemoveRight.substring(0, last.length))
        else if(last.endsWith(toRemoveRight))
          Some((StringLiteral(last.substring(0, last.length - toRemoveRight.length)) :: lReverseTail).reverse)
        else None
      case _ => None
    }

    def dropLeftIfPossible(l: List[Expr], toRemoveLeft: String): Option[List[Expr]] =
      if(toRemoveLeft == "") Some(l) else l match {
        case Nil => None
        case StringLiteral(first) :: lTail =>
          if(toRemoveLeft.startsWith(first))
            dropLeftIfPossible(lTail, toRemoveLeft.substring(0, first.length))
          else if(first.startsWith(toRemoveLeft))
            Some(StringLiteral(first.substring(toRemoveLeft.length)) :: lTail)
          else None
        case _ => None
      }

    newOut match {
      case StringLiteral(s) =>
        functionValue match {
        case StringLiteral(t) =>(
          if(t.startsWith(s)) {
            val StringConcats(seq) = function
            dropRightIfPossible(seq.reverse, t.substring(s.length)).toStream.map(x => ProgramFormula(StringConcats(x), Formula(known = Map(), varsToAssign = Set(), program.freeVars)))
          } else Stream.empty) #::: (
          if(t.endsWith(s)) {
            val StringConcats(seq) = function
            dropLeftIfPossible(seq, t.substring(0, t.length - s.length)).toStream.map(x => ProgramFormula(StringConcats(x), Formula(known = Map(), varsToAssign = Set(), program.freeVars)))
          } else Stream.empty
          )
          case _ => Stream.empty
        }
      case _ => Stream.empty
    }
  }*/
}
