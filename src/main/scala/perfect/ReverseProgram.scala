package perfect

import inox.Identifier
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import perfect.ProgramFormula.{PatternMatch, StringInsert}

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

  var experimentalUnifyLambda = false
  /** Returns the stream b if a is empty, else only a. */
  def ifEmpty[A](a: Stream[A])(b: =>Stream[A]): Stream[A] = {
    if(a.isEmpty) b else a
  }

  def put(outProg: ProgramFormula, prevIn: Option[Expr]): Stream[Expr] = {
    if(prevIn == None) {
      val outExpr = outProg.bodyDefinition.getOrElse(throw new Exception(s"Ill-formed program: $outProg"))
      return Stream(outExpr)
    }
    implicit val symbols = defaultSymbols.withFunctions(ReverseProgram.funDefs)
    implicit val cache = new HashMap[Expr, Expr]
    val newMain = FreshIdentifier("main")
    for { r <- repair(ProgramFormula(prevIn.get), outProg)
          ProgramFormula(newOutExpr, f) = r.insertVariables()
          _ = Log("Remaining formula: " + f)
          _ = Log("Remaining expression: " + newOutExpr)
          assignments <- f.determinizeAll(exprOps.variablesOf(newOutExpr).toSeq)
          _ = Log("Found assignments: " + assignments)
          finalNewOutExpr = exprOps.replaceFromSymbols(assignments, newOutExpr)
          _ = Log("Final  expression: " + finalNewOutExpr)
    } yield finalNewOutExpr
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

  /** Eval function. Uses a cache normally*/
  def evalWithCache(expr: Expr)(implicit cache: Cache, symbols: Symbols) = cache.getOrElseUpdate(expr, {
    import evaluators._
    val funDef = mkFunDef(FreshIdentifier("main"))()(stp => (Seq(), expr.getType, _ => expr))
    val p = InoxProgram(context, symbols)
    val evaluator = LambdaPreservingEvaluator(p)
    evaluator.eval(expr) match {
      case EvaluationResults.Successful(e) => e
      case m => throw new Exception(s"Could not evaluate: $expr, got $m")
    }
  })

  def maybeEvalWithCache(expr: Expr)(implicit cache: Cache, symbols: Symbols): Option[Expr] = {
    if(cache.contains(expr)) {
      Some(cache(expr))
    } else {
      import evaluators._
      val funDef = mkFunDef(FreshIdentifier("main"))()(stp => (Seq(), expr.getType, _ => expr))
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

    // Accelerators
    optVar(newOut).flatMap(newOutFormula.findConstraintValue).getOrElse(newOut) match {
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

    if(!newOut.isInstanceOf[Variable] && functionValue.nonEmpty && !functionValue.get.isInstanceOf[FiniteMap]  && functionValue.get == newOut) return {
      Log("@return original function");
      Stream(program.assignmentsAsOriginals())
    }
    //Log(s"functionValue ($functionValue) != newOut ($newOut)")

    //Log.prefix(s"@return ") :=
    def maybeWrappedSolutions = if(functionValue.isEmpty) Stream.empty else (function.getType match {
        case a: ADTType if !newOut.isInstanceOf[Variable] =>
          function match {
            case l: Let => Stream.empty[ProgramFormula] // No need to wrap a let expression, we can always do this later. Indeed,
              //f{val x = A; B} = {val x = A; f(B)}
            case Application(Lambda(_, _), _) => Stream.empty[ProgramFormula] // Same argument
            case _ if ProgramFormula.ListInsert.unapply(newOutProgram).nonEmpty => Stream.empty[ProgramFormula]
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
    def originalSolutions : Stream[ProgramFormula] =
      function match {
        // Values (including lambdas) should be immediately replaced by the new value
        case l: Literal[_] =>
          import ProgramFormula._
          optVar(newOut).flatMap(newOutFormula.findConstraintValue).getOrElse(newOut) match {
            case l: Literal[_] => // Raw replacement
              Stream(newOutProgram)

            case PatternMatch.Expr(before, variables, forClone) =>
              val newExpr = before
              before match {
                case lBefore: Literal[_] =>
                  Stream(ProgramFormula(newExpr))
                case vBefore: Variable =>
                  val value = variables.collectFirst{
                    case (v, value) if v == vBefore => value
                  }
                  value.toStream.map(value =>
                    ProgramFormula(newExpr, Formula(vBefore -> InsertVariable(value)))
                  )
                case StringConcat(a, b) =>
                  val newFormula = Formula(exprOps.variablesOf(before).map(v => v -> InsertVariable(variables.collectFirst{
                    case (v2, value) if v2 == v => value
                  }.get)).toMap)
                  Stream(ProgramFormula(newExpr, newFormula))
                case op => throw new Exception("Operation not supported in pattern matching: " + op)
              }
              /*              def first = if(program.canDoWrapping) { // Insert let-expressions the closest to the use.
                              val outputExpr = CloneTextMultiple.assignmentDirect(textVarRights)(newExpr)
                              Stream(ProgramFormula(outputExpr))
                            } else Stream.empty*/
              // first #::: {
            // }

            case ProgramFormula.PasteVariable.Expr(left, v2, v2_value, right, direction) =>
              val newExpr = StringLiteral(left) +<>& v2 +<>& StringLiteral(right)
              Stream(ProgramFormula(newExpr, newOutFormula))

            case ProgramFormula.StringInsert.Expr(left, inserted, right, direction) =>
              Stream(ProgramFormula(StringLiteral(left + inserted + right)))

            case m: MapApply =>
              repair(program, newOutProgram.subExpr(newOutProgram.formula.findConstraintVariableOrLiteral(m)))
            case v: Variable =>
                // Replacement with the variable newOut, with a maybe clause.
              Stream(newOutProgram combineWith Formula(v -> OriginalValue(l)))
            case _ => Log(s"[Internal warning] Don't know what to do to replace a literal by this: $newOutProgram")
              Stream(newOutProgram)
          }

        case l: FiniteSet => // TODO: Need some rewriting to keep the variable's order.
          lazy val evaledElements = l.elements.map{ e =>
            (evalWithCache(functionFormula.assignments.get(e)), e)
          }
          def insertElementsIfNeeded(fs: FiniteSet) = {
            val expectedElements = fs.elements.toSet
            val newElements = evaledElements.filter{
              case (v, e) => expectedElements contains v
            }.map(_._2) ++ expectedElements.filter(x =>
              !evaledElements.exists(_._1 == x))
            Stream(newOutProgram.subExpr(FiniteSet(newElements, fs.base)))
          }

          if(isValue(l) && (newOut.isInstanceOf[FiniteSet] || newOut.isInstanceOf[Variable])) { // We shuold keep the same order if possible.
            optVar(newOut).flatMap(newOutFormula.findConstraintValue).getOrElse(newOut) match {
              case fs: FiniteSet =>
                insertElementsIfNeeded(fs)
              case _ =>
                Stream(newOutProgram)
            }
          } else {
            optVar(newOut).flatMap(newOutFormula.findConstraintValue).getOrElse(newOut) match {
              case fs: FiniteSet =>
                // Since there is no order, there is no point repairing expressions,
                // only adding new ones and deleting old ones.
                insertElementsIfNeeded(fs)

              case newOut => // Maybe it has a formula ?
                Stream(newOutProgram)
            }
          }
        case l: FiniteMap =>
          if(isValue(l) && (newOut.isInstanceOf[FiniteMap] || newOut.isInstanceOf[Variable])) {
            def reoderIfCanReorder(fm: FiniteMap) = {
              if(fm.pairs.forall(x => isValue(x._1))) { // Check that all the keys are values.
                val inserted = fm.pairs.filter(x => l.pairs.forall(y => x._1 != y._1))
                val fmUpdated = FiniteMap(l.pairs.flatMap {
                  case (key, value) => fm.pairs.collectFirst { case (k, v) if k == key => key -> v }
                } ++ inserted, fm.default, fm.keyType, fm.valueType)
                Stream(newOutProgram.subExpr(fmUpdated))
              } else Stream(newOutProgram)
            }
            optVar(newOut).flatMap(newOutFormula.findConstraintValue).getOrElse(newOut) match {
              case fm: FiniteMap => reoderIfCanReorder(fm)
              case newOut => Stream(newOutProgram)
            }
          } else {
            // Check for changed keys, removals and additions.
            lazy val partEvaledPairs = l.pairs.map{ case (key, value) =>
              (evalWithCache(functionFormula.assignments.get(key)), (key, value, evalWithCache(functionFormula.assignments.get(value))))
            }
            def propagateChange(fm: FiniteMap) = {
              val insertedPairs = fm.pairs.collect {
                case (k, v) if !partEvaledPairs.exists(x => x._1 == k) =>
                  Stream((k, ProgramFormula(v)))
              }

              val (newFiniteMapKV) = (ListBuffer[Stream[(Expr, ProgramFormula)]]() /: partEvaledPairs) {
                case (lb, (key_v, (key, value, value_v))) =>
                  val i = fm.pairs.lastIndexWhere(_._1 == key_v)
                  if(i > -1) {
                    val newValue = fm.pairs(i)._2
                    lb += repair(program.subExpr(value), newOutProgram.subExpr(newValue)).map(pf => (key, pf))
                  } else {
                    lb
                  }
              }.toList ++ insertedPairs
              for {solution <- inox.utils.StreamUtils.cartesianProduct(newFiniteMapKV)
                   (mapKeys, mapValuesFormula) = solution.unzip
                   mapValues = mapValuesFormula.map(_.expr)
                   mapFormula = mapValuesFormula.map(_.formula)
                   formula = (Formula() /: mapFormula){ case (f, ff) => f combineWith ff }
              } yield {
                ProgramFormula(FiniteMap(mapKeys.zip(mapValues), l.default, l.keyType, l.valueType), formula)
              }
            }
            optVar(newOut).flatMap(newOutFormula.findConstraintValue).getOrElse(newOut) match {
              case fm: FiniteMap => propagateChange(fm)
              case _ =>
                val insertedPairs = newOut match {
                  case v: Variable =>
                    Log("replacement by a variable - checking for inserted pairs")

                    newOutFormula.findConstraintValue(v) match {
                      case Some(np: FiniteMap) =>
                        Log(s"replacement by a variable - pairs in $np")
                        np.pairs.filter {
                          case (k, v) => !partEvaledPairs.exists(x => x._1 == k)
                        }
                      case _ => Nil
                    }
                  case _ => Nil
                }
                Log(s"inserted pairs: $insertedPairs")
                // We output the constraints with the given FiniteMap description.
                // We repair symbolically on every map's value.
                val repairs = partEvaledPairs.map {
                  case (key_v, (key, value, value_v)) =>
                    repair(program.subExpr(value), newOutProgram.subExpr(MapApply(newOut, key))).map((key_v, _))
                }
                for {keys_pf_seq <- inox.utils.StreamUtils.cartesianProduct(repairs)} yield {
                  val (keys, pf_seq) = keys_pf_seq.unzip
                  val (list_m, formula) = combineResults(pf_seq)
                  val new_exprs = keys.zip(list_m).toMap
                  // Keep the original order.
                  val newPairs = (partEvaledPairs map {
                    case (key_v, (key, value, value_v)) => key -> new_exprs(key_v)
                  }) ++ insertedPairs
                  ProgramFormula(
                    FiniteMap(newPairs, l.default, l.keyType, l.valueType),
                    formula)
                }
              //case _ => throw new Exception("Don't know what to do, not a Literal or a Variable: " + newOut)
            }

          }
        case fun@Lambda(vds, body) =>
          // Error if the free variables in body are not present in output.

          def unify: Stream[ProgramFormula] = {
            if(experimentalUnifyLambda && exprOps.variablesOf(fun).nonEmpty) {
              newOut match {
                case Lambda(vds2, body2) =>
                  val freshVariables1 = vds.map(vd => Variable(FreshIdentifier(vd.id.name, true), vd.tpe, vd.flags))
                  val freshBody1 = exprOps.replaceFromSymbols(vds.zip(freshVariables1).toMap, body)
                  val freshBody2 = exprOps.replaceFromSymbols(vds2.zip(freshVariables1).toMap, body2)
                  for{ pf <- repair(program.subExpr(freshBody1), newOutProgram.subExpr(freshBody2)) } yield {
                    pf.wrap { newBody =>
                      val abstractedBody = exprOps.replaceFromSymbols(freshVariables1.map(_.toVal).zip(vds.map(_.toVariable)).toMap, pf.expr)
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
          newOutProgram match {
            case ProgramFormula.PasteVariable(left, v2, v_value, right, direction) =>
              functionValue match {
                case Some(StringLiteral(s)) =>
                  def insertLeft = (if(left == s) {
                    if(right != "") {
                      Stream(ProgramFormula(v +& v2 +& StringLiteral(right)))
                    } else {
                      Stream(ProgramFormula(v +& v2))
                    }
                  } else Stream.empty) /:: Log.insertLeft
                  def insertRight = (if(right == s) {
                    if(left != "") {
                      Stream(ProgramFormula(StringLiteral(left) +& v2 + v))
                    } else {
                      Stream(ProgramFormula(v +& v2))
                    }
                  } else Stream.empty) /:: Log.insertRight

                  def propagate = (if(left != s && right != s &&
                    s.startsWith(left) && s.endsWith(right) &&
                    s.length >= left.length + right.length ) {
                    // We need to propagate this paste to higher levels.
                    Stream(ProgramFormula(v, newOutFormula combineWith (v -> StrongValue(newOutProgram.expr))))
                  } else Stream.empty) /:: Log.propagate
                  insertLeft #::: insertRight #::: propagate

                case _ => Stream.empty
              }
            case _ =>
              Stream(ProgramFormula(v, Formula(v -> StrongValue(newOut)) combineWith newOutFormula))
          }

        case Let(vd, expr, body) =>
          repair(ProgramFormula(Application(Lambda(Seq(vd), body), Seq(expr)), program.formula),
            newOutProgram).map {
            case ProgramFormula(Application(Lambda(Seq(vd), body), Seq(expr)), f) =>
              ProgramFormula(Let(vd, expr, body), f)
            case e  => throw new Exception(s"Don't know how to get a Let back from $e")
          }

        case StringConcat(expr1, expr2) =>
          optVar(newOutProgram.expr).flatMap(newOutFormula.findConstraintValue).
            map(v => ProgramFormula(v, newOutFormula)).getOrElse(newOutProgram) match {
            case pf@ProgramFormula.PatternMatch(before, variables, forClone) =>
              before match {
                case StringConcats.Exhaustive(patterns) =>
                  val values: List[String] = patterns.map{ pattern =>
                    val StringLiteral(a) = ProgramFormula(pattern, Formula(variables.map{
                      case (v, value) => v -> StrongValue(value)}.toMap )).functionValue
                    a
                  }
                  val Some(StringLiteral(originalLeft)) = maybeEvalWithCache(functionFormula.assignments.get(expr1))
                  val Some(StringLiteral(originalRight)) = maybeEvalWithCache(functionFormula.assignments.get(expr2))
                  val shortestTailForLeft = values.inits.toList.reverse.find{
                    case l => l.mkString("").startsWith(originalLeft)
                  }.get
                  val coverage = shortestTailForLeft.mkString("")
                  if(coverage == originalLeft) {
                    val newLeftPattern = StringConcats(patterns.take(shortestTailForLeft.length))
                    val newRightPattern = StringConcats(patterns.drop(shortestTailForLeft.length))
                    val arguments = List(
                      repair(program.subExpr(expr1), pf.subExpr(PatternMatch.Expr(newLeftPattern, variables, forClone))),
                      repair(program.subExpr(expr2), pf.subExpr(PatternMatch.Expr(newRightPattern, variables, forClone))))
                    for{ regroupped <- regroupArguments(arguments)
                         (Seq(newLeft1, newLeft2), formula) = regroupped
                    } yield {
                      ProgramFormula(StringConcat(newLeft1, newLeft2), formula)
                    }
                  } else {
                    Log(s"coverage: `$coverage`")
                    Log(s"origleft: `$originalLeft`")
                    // shortestTailForLeft contains the originalLeft. We need to split the last variable.
                    val lastValue: String = values(shortestTailForLeft.length-1)
                    val extra = lastValue.length - (coverage.length - originalLeft.length) // > 0
                    patterns(shortestTailForLeft.length - 1) match {
                      case s: StringLiteral => // We can just split the string literal into two.
                        repair(program, PatternMatch(StringConcats(
                          patterns.take(shortestTailForLeft.length - 1) ++
                          List(StringLiteral(lastValue.substring(0, extra)),
                          StringLiteral(lastValue.substring(extra))) ++
                          patterns.drop(shortestTailForLeft.length)
                        ), variables, forClone))
                      case lastVar: Variable => // Way interesting, we need to split the variable
                        val leftVar = Variable(FreshIdentifier(Utils.uniqueName(lastVar.id.name, Set(lastVar.id.name))), StringType, Set())
                        val rightVar = Variable(FreshIdentifier(Utils.uniqueName(lastVar.id.name, Set(lastVar.id.name, leftVar.id.name))), StringType, Set())
                        val newFormula = Formula(Map(
                          lastVar -> InsertVariable(leftVar +& rightVar),
                          leftVar -> InsertVariable(StringLiteral(lastValue.substring(0, extra))),
                          rightVar -> InsertVariable(StringLiteral(lastValue.substring(extra)))))
                        val newLeftPattern = StringConcats(
                          patterns.take(shortestTailForLeft.length - 1) ++
                          List(leftVar))
                        val newRightPattern = StringConcats(List(rightVar) ++
                          patterns.drop(shortestTailForLeft.length)
                        )

                        val newVariables = variables.filter(_._1 != lastVar) ++
                          List((leftVar, StringLiteral(lastValue.substring(0, extra))),
                            (rightVar, StringLiteral(lastValue.substring(extra))))

                        val arguments = List(
                          repair(program.subExpr(expr1), pf.subExpr(PatternMatch.Expr(newLeftPattern, newVariables, forClone))),
                          repair(program.subExpr(expr2), pf.subExpr(PatternMatch.Expr(newRightPattern, newVariables, forClone))))
                        for{ regroupped <- regroupArguments(arguments)
                             (Seq(newLeft1, newLeft2), formula) = regroupped
                        } yield {
                          ProgramFormula(StringConcat(newLeft1, newLeft2), formula combineWith newFormula)
                        }

                      case e => throw new Exception(s"[internal error] Only variables and strings in string patterns, got $e")
                    }
                  }
              }

            case _ =>
              ifEmpty(for (pf <- repair(program.subExpr(FunctionInvocation(StringConcatLens.identifier, Nil,
                Seq(expr1, expr2))), newOutProgram)) yield {
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
                  case ProgramFormula.StringInsert(left, inserted, right, direction)
                    if !expr1.isInstanceOf[StringLiteral] && !expr2.isInstanceOf[StringLiteral] &&
                      maybeEvalWithCache(functionFormula.assignments.get(expr1)) == Some(StringLiteral(left)) &&
                      maybeEvalWithCache(functionFormula.assignments.get(expr2)) == Some(StringLiteral(right))
                  => Stream(program.subExpr(expr1 +& StringLiteral(inserted) +& expr2).assignmentsAsOriginals())
                  case _ => Stream.empty[ProgramFormula]
                }
              }
          }

        case ADT(adtType@ADTType(tp, tpArgs), argsIn) =>
          newOut match {
            case ProgramFormula.PatternMatch.Expr(pattern, variables, forClone) =>
              pattern match {
                case ADT(adtType2, argsIn2) if adtType2 == adtType =>
                  val argumentsRepaired = for{ (argIn, argIn2) <- argsIn.zip(argsIn2) } yield {
                    repair(program.subExpr(argIn),
                      newOutProgram.subExpr(
                        ProgramFormula.PatternMatch.Expr(
                          argIn2, variables, forClone
                        )
                      )
                    )
                  }
                  for{ res <- regroupArguments(argumentsRepaired)
                       (newArgs, formula) = res
                  } yield {
                    ProgramFormula(ADT(adtType, newArgs), formula)
                  }

                case v: Variable if variables.indexWhere(_._1 == v) >= 0 =>
                  val value = variables.collectFirst{ case (`v`, value) => value  }.get
                  // Normally the value equals functionValue, so no need to call it.
                  Stream(ProgramFormula(v, Formula(v -> InsertVariable(value))))

                case _ => throw new Exception("Did not expect something else than an ADT of same type or variable here")
              }

            case ProgramFormula.PatternReplace.Expr(before, variables, after) =>
              before match { // TODO: Pattern replace at higher level?
                case ADT(adtType2, argsIn2) if adtType2 == adtType =>
                  val argsMatched = argsIn.zip(argsIn2).map{
                    case (expr, pattern) =>
                      repair(
                        program.subExpr(expr),
                        newOutProgram.subExpr(
                          ProgramFormula.PatternMatch.Expr(
                            pattern, variables, false
                          )))
                  }
                  for{ argumentsCombined <-regroupArguments(argsMatched)
                       (_, formula) = argumentsCombined
                  } yield ProgramFormula(after, formula)

                case v: Variable =>
                  ???

                case _ => throw new Exception("Did not expect something else than an ADT of same type or variable here")
              }
            case ProgramFormula.ListInsert.Expr(tpe, before, inserted, after) =>
              Log("ListInsert")
              if(before.length == 0) { // Insertion happens before this element
                Log("beforeLength == 0")
                // We might delete the elements afterwards.
                if(after.length == 0) {
                  Log("afterLength == 0")
                  Stream(
                    ProgramFormula(ListLiteral(inserted, tpe), newOutFormula)
                  )
                } else { // after.length > 0
                  Log("afterLength > 0")
                  functionValue match {
                    case Some(ListLiteral(functionValueList, tpe)) =>
                      val newTail = ListLiteral(functionValueList.tail, tpe)

                      if(after.length == functionValueList.length) { // No deletion.
                        Log("afterLength == functionValueList.length")
                        for{ pf <- repair(program.subExpr(argsIn(0)).withComputedValue(functionValueList.head), newOutProgram.subExpr(after.head))
                             pf2 <- repair(program.subExpr(argsIn(1)).withComputedValue(newTail),
                               ProgramFormula.ListInsert(tpe, Nil, Nil, after.tail) combineWith newOutFormula) } yield {
                          ProgramFormula(ListLiteral.concat(
                            ListLiteral(inserted, tpe),
                            ListLiteral(List(pf.expr), tpe),
                            pf2.expr), pf.formula combineWith pf2.formula combineWith newOutFormula)
                        }
                      } else {
                        Log("afterLength < functionValueList.length")
                        assert(after.length < functionValueList.length) // some deletion happened.
                        val updatedOutProgram = ProgramFormula.ListInsert(tpe, Nil, Nil, after) combineWith newOutFormula // Recursive problem if
                        for{ pf <- repair(program.subExpr(argsIn(1)).withComputedValue(newTail), updatedOutProgram)} yield {
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
                val updatedOutProgram = ProgramFormula.ListInsert(tpe, before.tail, inserted, after) combineWith newOutFormula

                for{pfHead <- repair(program.subExpr(argsIn(0)), newOutProgram.subExpr(before.head))
                    pfTail <- repair(program.subExpr(argsIn(1)), updatedOutProgram)} yield {
                  ProgramFormula(ListLiteral.concat(ListLiteral(List(pfHead.expr), tpe), pfTail.expr),
                    pfHead.formula combineWith pfTail.formula
                  )
                }
              }

            case v: Variable =>
              Stream(newOutProgram)
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
                   (newArgs, assignments) = combineResults(seq)
              } yield {
                ProgramFormula(ADT(ADTType(tp2, tpArgs2), newArgs), assignments)
              }
            case ADT(ADTType(tp2, tpArgs2), args2) =>
              Log("ADT 3")
              Stream.empty // Wrapping already handled.

            case a =>
              throw new Exception(s"Don't know how to handle this case : $a is supposed to be put in place of a ${tp}")
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

        case MapApply(map, key) => // Variant of ADT selection.
          val map_v = evalWithCache(functionFormula.assignments.get(map)).asInstanceOf[FiniteMap] //originalAdtValue
          val key_v = evalWithCache(functionFormula.assignments.get(key))

          val defaultValue = map_v.default

          val vds = map_v.pairs.map{ case (k, v) => (k, Variable(FreshIdentifier("x", true), map_v.valueType, Set()))}
          var found = false
          val constraints = (vds map {
            case (k, vd) => if(k == key_v) {
              found = true
              vd -> StrongValue(newOut)
            } else {
              vd -> OriginalValue(evalWithCache(MapApply(map_v, k)))
            }
          }).toMap
          val finiteMapRepair = if (!found) { // We should not change the default, rather add a new entry.
            FiniteMap(vds.map{x => (x._1, x._2)} :+ (key_v -> newOut)
              , map_v.default, map_v.keyType, map_v.valueType)
          } else {
            FiniteMap(vds.map{x => (x._1, x._2)}, map_v.default, map_v.keyType, map_v.valueType)
          }

          val newConstraint = Formula(constraints)

          for{ pf <- repair(program.subExpr(map), newOutProgram.subExpr(finiteMapRepair) combineWith newConstraint) } yield {
            pf.wrap(x => MapApply(x, key))
          }

        case Application(lambdaExpr, arguments) =>
          val originalValueMaybe: Option[Expr] = (lambdaExpr match {
            case v: Variable => currentValues.get(v).map(_.getValue).flatten.orElse(maybeEvalWithCache(functionFormula.assignments.get(v)))
            case l: Lambda => Some(l)
            case l => maybeEvalWithCache(functionFormula.assignments.get(l))
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
              val freshBody = exprOps.replaceFromSymbols(oldToFresh, body)
              val argumentVals = arguments.map(arg => maybeEvalWithCache(functionFormula.assignments.get(arg)).map(v => OriginalValue(v)))
              if(argumentVals.forall(_.nonEmpty)) {
                val argumentValues = freshArgsNames.zip(argumentVals.map(_.get)).toMap
                val freshFormula = Formula(argumentValues)
                val newpf = (program.subExpr(freshBody) combineWith freshFormula).wrappingEnabled
                for {pf <- repair(newpf, newOutProgram) /:: Log.prefix(s"For repair$stackLevel, recovered:\n")
                     ProgramFormula(newBodyFresh, newBodyFreshFormula) = pf
                     newBody = exprOps.replaceFromSymbols(freshToOld, newBodyFresh)
                     isSameBody = (newBody == body) /: Log.isSameBody
                     args <-
                     combineArguments(program,
                       arguments.zip(freshArgsNames).map { case (arg, expected) =>
                         (arg, newOutProgram.subExpr(expected) combineWith newBodyFreshFormula combineWith Formula(expected -> argumentValues(expected)))
                       })
                     (newArguments, newArgumentsFormula) = args
                     newLambda = if (isSameBody) originalValue else Lambda(argNames, newBody)
                     pfLambda <- lambdaExpr match {
                       case v: Variable => Stream(ProgramFormula(v, (
                         if (isSameBody) Formula() else
                           Formula(v -> StrongValue(newLambda)))))
                       case l => repair(ProgramFormula(l, program.formula),
                         newOutProgram.subExpr(newLambda) combineWith newBodyFreshFormula)
                     }
                     ProgramFormula(newAppliee, lambdaRepairFormula) = pfLambda
                     finalApplication = Application(newAppliee, newArguments) /: Log.prefix("finalApplication")
                } yield {
                  Log(s"newBodyFreshFormula: $newBodyFreshFormula")
                  Log(s"lambdaRepairFormula: $lambdaRepairFormula")
                  Log(s"newArgumentsFormula: $newArgumentsFormula")
                  val combinedFormula = newBodyFreshFormula combineWith lambdaRepairFormula combineWith newArgumentsFormula
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

                    def modifyFunction: Stream[ProgramFormula] = {
                      if (originalVariables.size == 1) { // No need to evaluate the arguments, we just unify.

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
                        // We try to evaluate everything else so that we only have unification to do.
                        val newArguments = arguments.map { arg =>
                          exprOps.preMap{
                            case Application(v: Variable, args2) if originalVariables contains v =>
                              maybeEvalWithCache(functionFormula.assignments.get(v)) match {
                                case Some(Lambda(nArg, nBody)) =>
                                  Some(exprOps.replaceFromSymbols(nArg.map(_.toVariable).zip(args2).toMap, nBody))
                                case _ => None
                              }
                            case v: Variable if originalVariables contains v => maybeEvalWithCache(functionFormula.assignments.get(v))
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
              val argsValue = args.map(arg => evalWithCache(functionFormula.assignments.get(arg))) // One day, args.map(arg => program.subExpr(arg))
              val lenseResult = lens.put(tpes)(argsValue, newOutProgram)
              for{l <- lenseResult; (newArgsValues, newForm) = l
                  a <- combineArguments(program, args.zip(newArgsValues))
                  (newArguments, newArgumentsFormula) = a
              } yield {
                val formula = newForm combineWith newArgumentsFormula
                ProgramFormula(FunctionInvocation(f, tpes, newArguments), formula)
              }
          }
        case SetAdd(sExpr, elem) =>
          val sExpr_v = evalWithCache(functionFormula.assignments.get(sExpr))
          val elem_v = evalWithCache(functionFormula.assignments.get(elem))
          val FiniteSet(vs, tpe) = sExpr_v
          val FiniteSet(vsNew, _) = newOut
          val vsSet = vs.toSet
          val vsNewSet = vsNew.toSet
          val maybeAddedElements = vsNewSet -- vsSet
          val maybeRemovedElements = vsSet -- vsNewSet
          val (changedElements, added, removed) = if(maybeAddedElements.size == 1 && maybeRemovedElements.size == 1) {
            (maybeRemovedElements.headOption.zip(maybeAddedElements.headOption).headOption: Option[(Expr, Expr)], Set[Expr](), Set[Expr]())
          } else
            (None: Option[(Expr, Expr)], maybeAddedElements: Set[Expr], maybeRemovedElements: Set[Expr])
          Log(s"Added $added, Removed $removed, changed: $changedElements")
          changedElements match {
            case Some((old, fresh)) =>
              (if(vsSet contains old) {
                Log.prefix("#1") :=
                  (for(pf <- repair(program.subExpr(sExpr),
                  newOutProgram.subExpr(FiniteSet((vsSet - old + fresh).toSeq, tpe)))) yield {
                  pf.wrap(x => SetAdd(x, elem))
                })
              } else Stream.empty) #::: (
                Log.prefix("#2") :=
                  (if(elem_v == old) {
                  for(pf <- repair(program.subExpr(elem), newOutProgram.subExpr(fresh))) yield {
                    pf.wrap(x => SetAdd(sExpr, x))
                  }
                } else Stream.empty)
              )
            case None => // Just added and removed elements.
              if(removed.isEmpty) { // Just added elements.
                for {pf <- repair(program.subExpr(sExpr),
                  newOutProgram.subExpr(FiniteSet((vsSet ++ (added - elem_v)).toSeq, tpe)))
                     pfElem <- repair(program.subExpr(elem), ProgramFormula(elem_v))
                } yield {
                  pf.wrap(x => SetAdd(x, pfElem.expr)) combineWith pfElem.formula
                }
              } else {
                if(removed contains elem_v) { // We replace SetAdd(f, v) by f
                  for(pf <- repair(program.subExpr(sExpr),
                    newOutProgram.subExpr(FiniteSet(vsSet.toSeq, tpe))
                  )) yield pf
                } else { // All changes happened in the single set.
                  for{pf <- repair(program.subExpr(sExpr),
                    newOutProgram.subExpr(FiniteSet((vsSet ++ (added-elem_v) -- removed).toSeq, tpe)))
                      pfElem <- repair(program.subExpr(elem), ProgramFormula(elem_v))
                  } yield pf.wrap(x => SetAdd(x, pfElem.expr)) combineWith pfElem.formula
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

    (if(program.isWrappingLowPriority) {
      interleave { originalSolutions } { maybeWrappedSolutions }
    } else {
      interleave { maybeWrappedSolutions } { originalSolutions }
    }) #::: {
//      ???
      Log(s"Finished repair$stackLevel"); Stream.empty[ProgramFormula]}  /:: Log.prefix(s"@return for repair$stackLevel(\n  $program\n, $newOutProgram):\n~>")
  }

  /** Given a sequence of (arguments expression, expectedValue),
      returns the cartesian product of all argument programs and solutions. */
  private def combineArguments(pf: ProgramFormula,
      arguments: Seq[(Expr, ProgramFormula)])(implicit symbols: Symbols, cache: Cache): Stream[(Seq[Expr], Formula)] = {
    Log(s"combining arguments for $pf")
    val argumentsReversed = arguments.map { case (arg, expected) =>
      Log(s"repairing argument $arg should equal $expected")
      repair(ProgramFormula(arg, pf.formula), expected)
    }
    regroupArguments(argumentsReversed)
  }

  // Given a ProgramFormula for each of the fields, returns a list of expr and a single formulas
  private def regroupArguments(arguments: Seq[Stream[ProgramFormula]])
                            (implicit symbols: Symbols, cache: Cache): Stream[(Seq[Expr], Formula)] = {
    inox.utils.StreamUtils.cartesianProduct(arguments).map{
      pfs =>
        (pfs.map(_.expr), (Formula() /: pfs) { case (f, pfr) => f combineWith pfr.formula })
    }
  }

  // Given a ProgramFormula for each of the fields, returns a list of expr and a single formulas
  private def combineResults(seq: List[ProgramFormula])
            (implicit symbols: Symbols, cache: Cache): (List[Expr], Formula) = {
    val (lb, f) = ((ListBuffer[Expr](), Formula()) /: seq) {
      case total@((ls, f1), (ProgramFormula(l, f2))) =>
        (ls += l, f1 combineWith f2)
    }
    (lb.toList, f)
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
