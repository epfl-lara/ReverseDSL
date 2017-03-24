package perfect

import inox.Identifier
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import scala.collection.mutable.{HashMap, ListBuffer}

/**
  * Created by Mikael on 03/03/2017.
  */
object ReverseProgram extends lenses.Lenses {
  type FunctionEntry = Identifier
  type ModificationSteps = Unit
  type OutExpr = Expr
  type Cache = HashMap[Expr, Expr]

  case class ProgramFormula(program: Expr, formula: Formula = Formula()) {
    assert((freeVars.filter(vd => !formula.varsToAssign(vd) && !formula.unchanged(vd))).isEmpty,
      s"This program is not well contrained by its formula $formula:\n$program")

    lazy val freeVars: Set[ValDef] = exprOps.variablesOf(program).map(_.toVal)

    override def toString = program.toString + s" [$formula]" + (if(canWrapInputString) " (wrapping enabled)" else "")
    var canWrapInputString = false

    def wrappingEnabled: this.type = {
      this.canWrapInputString = true
      this
    }

    def withComputedValue(e: Expr): this.type = {
      givenValue = Some(e)
      this
    }

    // Can be set-up externally to bypass the computation of the function value.
    // Must be set before a call to functionValue using .withComputedValue
    private var givenValue: Option[Expr] = None

    def functionValue(implicit cache: Cache, symbols: Symbols): Expr = {
      givenValue match {
        case Some(e) => e
        case None =>
          val res = if((freeVars -- formula.known.keySet).isEmpty) {
            evalWithCache(letm(formula.known) in program)
          } else {
            throw new Exception(s"[Internal error] Tried to compute a function value but not all variables were known. $this")
          }
          givenValue = Some(res)
          res
      }
    }

    /** Uses the result of a programFormula by wrapping the expression */
    def wrap(f: Expr => Expr): ProgramFormula = {
      ProgramFormula(f(program), formula)
    }

    /** Replaces the expression with another, for defining sub-problems mostly. */
    def subExpr(f: Expr): ProgramFormula = {
      ProgramFormula(f, formula)
    }

    /** Augment this program with the given formula */
    def combineWith(f: Formula): ProgramFormula = {
      ProgramFormula(program, formula combineWith f)
    }
  }

  object Formula {
    def maybeDefault(e: Set[ValDef], values: Map[ValDef, Expr]): Formula = {
      Formula(Map(), Set(), e) //and(e.toSeq.map{ v => E(Utils.maybe)(v.toVariable === values(v))}: _*))
    }
  }

  case class Formula(known: Map[ValDef, Expr] = Map(),
                     varsToAssign: Set[ValDef] = Set(),
                     unchanged: Set[ValDef] = Set(),
                     unknownConstraints: Expr = BooleanLiteral(true)) { // Can contain middle free variables.
    assert((known.keySet -- varsToAssign).isEmpty, s"Formula with wrong set of vars to assign: ${known} should have its variables in ${varsToAssign}")
    assert((unchanged intersect varsToAssign).isEmpty, s"Formula with incoherent set of variables to assign and unchanged: $this")
    assert(((varsToAssign -- exprOps.variablesOf(unknownConstraints).map(_.toVal)) -- known.keys).toList.isEmpty, s"Underconstrained formula: $this")
    assert(unchanged.forall(x => !unknownConstraintsVars(x)), s"A value is said unchanged but appears in constraints: $this")

    def combineWith(other: Formula): Formula = {
      val newCs = unknownConstraints &<>& other.unknownConstraints
      val conflict = (known.keySet intersect other.known.keySet).filter{ k => known(k) != other.known(k) }
      val assignmentsForSure = known ++ other.known -- conflict
      val newVarsToAssign =  varsToAssign ++ other.varsToAssign
      val newUnchangedVars = unchanged ++ other.unchanged -- newVarsToAssign
      if(conflict.nonEmpty) {
        val maybeAssignments = and(conflict.toSeq.map{ k => k.toVariable === known(k) || k.toVariable === other.known(k)}: _*)
        Formula(assignmentsForSure, newVarsToAssign, newUnchangedVars, newCs &<>& maybeAssignments)
      } else {
        Formula(assignmentsForSure, newVarsToAssign, newUnchangedVars, newCs)
      }
    }

    override def toString = "["+known.toSeq.map{ case (k, v) => k.id + "->" + v}.mkString("(",",",")")+", " +
      "vs:" + varsToAssign.toSeq.map(_.id).mkString("{", ",", "}") + ", " +
      "vl:" + unchanged.toSeq.map(_.id).mkString("{", ",", "}") + ", " +
    unknownConstraints.toString() + "]"
    private lazy val unknownConstraintsVars: Set[ValDef] = exprOps.variablesOf(unknownConstraints).map(_.toVal)

    /** Returns an expression equal to the value of vd*/
    def getOrElse(vd: ValDef, e: =>Expr): Expr = {
      known.getOrElse(vd, {
        /*val TopLevelAnds(ands) = unknownConstraints
        ands.collectFirst{
          case Equals(x, y) => x ==
        }*/
        if(varsToAssign(vd)) {
          vd.toVariable
        } else e // The expression is unchanged, we return the original expression
      })
    }

    // The assignments and the formula containing the other expressions.
    def determinizeAll(freeVariables: Seq[ValDef] = varsToAssign.toSeq)(implicit symbols: Symbols): Stream[Map[ValDef, Expr]] = {

      Log(s"Trying to get all solutions for $varsToAssign of \n" + this)
      //val freeVariables = varsToAssign.toSeq

      unknownConstraints match {
        case BooleanLiteral(true) => Stream(freeVariables.map(fv => fv -> known(fv)).toMap)
        case BooleanLiteral(false) => Stream.empty
        case _ =>
          val input = Variable(FreshIdentifier("input"), tupleTypeWrap(freeVariables.map(_.getType)), Set())
          //println(s"input is of type ${input.getType}")
          val constraint = InoxConstraint(input === tupleWrap(freeVariables.map(_.toVariable)) && unknownConstraints && and(known.toSeq.map{ case (k, v) => k.toVariable === v} : _*))
          Log(s"Solving for $constraint")
          constraint.toStreamOfInoxExpr(input).map {
            case Tuple(args) => freeVariables.zip(args).map{ case (fv: ValDef, expr: Expr) => fv -> expr }.toMap
            case e if freeVariables.length == 1 =>
              Map(freeVariables.head -> e)
            case e =>
              Log("other solution : " + e)
              Map[ValDef, Expr]()
          }
      }
    }

    /* Force the evaluation of the constraints to evaluate an expression*/
    def evalPossible(e: Expr)(implicit cache: Cache, symbols: Symbols): Stream[Expr] = {
      for(assignment <- determinizeAll()) yield {
        evalWithCache(letm(known ++ assignment) in e)
      }
    }
  }

  import Utils._
  import InoxConvertible._
  lazy val context = Context.empty.copy(options = Options(Seq(optSelectedSolvers(Set("smt-cvc4")))))

  implicit class BooleanSimplification(f: Expr) {
    @inline def &<>&(other: Expr): Expr = other match {
      case BooleanLiteral(true) => f
      case BooleanLiteral(false) => other
      case _ => f match {
        case BooleanLiteral(true) => other
        case BooleanLiteral(false) => f
        case _ => f && other
      }
    }
  }

  def ifEmpty[A](a: Stream[A])(b: =>Stream[A]): Stream[A] = {
    if(a.isEmpty) b else a
  }

  def put[A: InoxConvertible](out: A, prevOut: Option[OutExpr], modif: Option[ModificationSteps], prevIn: Option[(InoxProgram, FunctionEntry)]): Iterable[(InoxProgram, FunctionEntry)] = {
    put(inoxExprOf[A](out), prevOut, modif, prevIn)
  }

    /** Reverses a parameterless function, if possible.*/
  def put(outExpr: Expr, prevOut: Option[OutExpr], modif: Option[ModificationSteps], prevIn: Option[(InoxProgram, FunctionEntry)]): Iterable[(InoxProgram, FunctionEntry)] = {
    if(prevIn == None) {
      implicit val symbols = defaultSymbols
      val main = FreshIdentifier("main")
      val fundef = mkFunDef(main)()(stp => (Seq(), outExpr.getType, _ => outExpr))
      return Stream((InoxProgram(context, Seq(fundef), allConstructors), main))
    }
    val (prevProgram, prevFunctionEntry) = prevIn.get
    implicit val symbols = prevProgram.symbols
    val prevFunction = prevProgram.symbols.functions.getOrElse(prevFunctionEntry, return Nil)
    val prevBody = prevFunction.fullBody
    val newMain = FreshIdentifier("main")
    implicit val cache = new HashMap[Expr, Expr]
    for { r <- repair(ProgramFormula(prevBody), outExpr)
         ProgramFormula(newOutExpr, f) = r
         _ = Log("Remaining formula: " + f)
         _ = Log("Remaining expression: " + newOutExpr)
         assignments <- f.determinizeAll(exprOps.variablesOf(newOutExpr).toSeq.map(_.toVal))
         _ = Log("Found assignments: " + assignments)
         finalNewOutExpr = exprOps.replaceFromSymbols(assignments, newOutExpr)
         _ = Log("Final  expression: " + finalNewOutExpr)
         newFunDef = mkFunDef(newMain)()(stp => (Seq(), prevFunction.returnType, _ => finalNewOutExpr))
         newProgram = InoxProgram(context, symbols.withFunctions(Seq(newFunDef)))
    } yield (newProgram, newMain)
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

  private case class letm(v: Map[ValDef, Expr]) {
    @inline def in(res: Expr) = {
      (res /: v) {
        case (res, (key, value)) => let(key, value)(_ => res)
      }
    }
  }

  /** Match lambda's bodies to recover the original assignments */
  def obtainMapping(originalInput: Expr, freeVars: Set[Variable], originalAssignments: Map[ValDef, Expr], output: Expr): Stream[Map[ValDef, Expr]] = {
    //Log.prefix(s"obtainMapping($originalInput, $freeVars, $originalAssignments, $output) =") :=
    (originalInput, output) match {
      case (v: Variable, l) =>
        if(freeVars(v)) {
          //Log(s"$v is a free variable")
          if(!(originalAssignments contains v.toVal) || l == originalAssignments(v.toVal)) {
            //Log(s"Value unchanged")
            Stream(Map())
          } else {
            //Log(s"Value updated: $l")
            Stream(Map(v.toVal -> l))
          }
        } else Stream(Map())
      case (Operator(subtrees, _), Operator(subtrees2, _)) =>
        if(subtrees.length == subtrees2.length) {
          inox.utils.StreamUtils.cartesianProduct(
            subtrees.zip(subtrees2).map{ case (a, b) => obtainMapping(a, freeVars, originalAssignments, b)}
          ).flatMap{ (e: Seq[Map[ValDef, Expr]]) =>
            def combineAll(remaining: Seq[Map[ValDef, Expr]], current: Map[ValDef, Expr]): Stream[Map[ValDef, Expr]] = {
              //Log(s"combineAll($remaining, $current)")
              remaining match {
              case Seq() =>
                //Log(s"returning $current")
                Stream(current)
              case head +: tail =>
                val intersection = inox.utils.StreamUtils.cartesianProduct(
                  (current.keySet intersect head.keySet).toSeq.map{ key =>
                    if(current(key) != head(key)) {
                      Stream(key -> current(key), key -> head(key))
                    } else {
                      Stream(key -> current(key))
                    }
                  } ++ (head.keySet -- current.keys).map{ key => Stream(key -> head(key))}
                ).map{ _.toMap }
                //Log(s"intersection = $intersection")
                if(intersection.nonEmpty) {
                  // We get all variants from the intersection
                  intersection.flatMap{ possiblity => combineAll(tail, current ++ possiblity )}
                } else combineAll(tail, current ++ head)
              }
            }
            combineAll(e, Map())
          }
        } else Stream.empty
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
    * @param newOut Either a literal value that should be produced by function, or a variable,
    *               in which case the result will have in the formula a constraint over this variable,
    *               Or a let-expression to denote a clone-and-paste.
    * @return A set of possible expressions, along with a set of possible assignments to input variables.
    **/
  def repair(program: ProgramFormula, newOut: Expr)
            (implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    val ProgramFormula(function, Formula(currentValues, _, _, _)) = program
    val stackLevel = Thread.currentThread().getStackTrace.length
    Log(s"\n@repair$stackLevel(\n  $program\n, $newOut)")
    if(function == newOut) return { Log("@return original");
      Stream(program.copy(formula = program.formula.copy(known = Map(), varsToAssign = Set())))
    }

    lazy val functionValue = program.functionValue

    if(functionValue == newOut) return {
      Log("@return original function");
      Stream(program.copy(formula = program.formula.copy(known = Map(), varsToAssign = Set(), unchanged = program.formula.known.keySet)))
    }

    //Log.prefix(s"@return ") :=
    interleave {
      function.getType match {
        case a: ADTType if !newOut.isInstanceOf[Variable] =>
          function match {
            case l: Let => Stream.empty[ProgramFormula] // No need to wrap a let expression, we can always do this later. Indeed,
              //f{val x = A; B} = {val x = A; f(B)}
            case Application(Lambda(_, _), _) => Stream.empty[ProgramFormula] // Same argument
            case _ =>
              maybeWrap(program, newOut, functionValue) #::: maybeUnwrap(program, newOut, functionValue)
          }
        case StringType if !newOut.isInstanceOf[Variable] && program.canWrapInputString =>
          function match {
            case l: Let => Stream.empty[ProgramFormula]
            case Application(Lambda(_, _), _) => Stream.empty[ProgramFormula]
            case _ =>
              // Stream.empty
              // Can be a StringConcat with constants to add or to remove.
              maybeWrapString(program, newOut, functionValue)// #::: maybeUnwrapString(program, newOut, functionValue)
          }
        case _ => Stream.empty[ProgramFormula]
      }
    } {
      function match {
        // Values (including lambdas) should be immediately replaced by the new value
        case l: Literal[_] =>
          newOut match {
            case v: Variable => // Replacement with the variable newOut, with a maybe clause.
              Stream(ProgramFormula(newOut, Formula(Map(), Set(), Set(v.toVal))))
            case l: Literal[_] => // Raw replacement
              Stream(ProgramFormula(newOut, Formula(Map(), Set(), Set())))
            /*case l@Let(cloned: ValDef, _, _) =>
              Stream(ProgramFormula(newOut, Formula(Map(), Set(), Set(), BooleanLiteral(true))))*/
            case _ => throw new Exception("Don't know what to do, not a Literal, a Variable, or a let: "+newOut)
          }
        case l: FiniteMap =>
          if(isValue(l)) {
            newOut match {
              case v: Variable => // Replacement with the variable newOut, with a maybe clause.
                val maybes = and(l.pairs.map {
                  case (key_v, value_v) => E(Utils.maybe)(MapApply(newOut, key_v) === value_v)
                }: _*)

                Stream(ProgramFormula(newOut, Formula(Map(), Set(v.toVal), Set(), maybes)))
              case fm: FiniteMap => // Raw replacement
                Stream(ProgramFormula(newOut, Formula(Map(), Set(), Set())))
              /*case l@Let(cloned: ValDef, _, _) =>
              Stream(ProgramFormula(newOut, Formula(Map(), Set(), Set(), BooleanLiteral(true))))*/
              case _ => throw new Exception("Don't know what to do, not a Literal or a Variable " + newOut)
            }
          } else {
            // Check for changed keys, removals and additions.
            lazy val partEvaledPairs = l.pairs.map{ case (key, value) =>
              (evalWithCache(letm(currentValues) in key), (key, value, evalWithCache(letm(currentValues) in value)))
            }
            newOut match {
              case v: Variable =>
                val insertedPairs = program.formula.unknownConstraints match {
                  case TopLevelAnds(ands) =>
                    ands.collectFirst[Seq[(Expr, Expr)]]{
                      case Equals(mapVar, FiniteMap(possiblyNewPairs, _, _, _))
                        if mapVar == v => possiblyNewPairs
                    } match {
                      case None => Nil
                      case Some(np) => np.filter{
                        case (k, v) => !partEvaledPairs.exists(x => x._1 == k)
                      }
                    }
                }
                // We output the constraints with the given FiniteMap description.
                // We repair symbolically on every map's value.
                val repairs = partEvaledPairs.map{
                  case (key_v, (key, value, value_v)) =>
                    repair(program.subExpr(value), MapApply(v, key))
                }
                for{pf_seq <- inox.utils.StreamUtils.cartesianProduct(repairs)} yield {
                  val (list_m, formula) = combineResults(pf_seq, currentValues)
                  val newPairs = (list_m.zip(partEvaledPairs) map {
                    case (e, (_, (key, value, _))) => key -> e
                  }) ++ insertedPairs
                  ProgramFormula(
                    FiniteMap(newPairs, l.default, l.keyType, l.valueType),
                    formula)
                }
                /*
                if(currentValues contains v.toVal) {
                  //val FiniteMap(original_pairs, _, _, _) = currentValues(v.toVal)
                  val repairedValues = partEvaledPairs.map{
                    case (key_v, (key, value, value_v)) =>
                      repair(program.subExpr(value), MapApply(v, key_v))
                  }
                  val linRepairedValues = inox.utils.StreamUtils.cartesianProduct(repairedValues)
                  for{pfs <- linRepairedValues} yield {
                    val (lExpr, formula) = combineResults(pfs, currentValues)
                    val expr = l.copy(pairs=l.pairs.zip(lExpr).map{ x => x._1._1 -> x._2})
                    ProgramFormula(expr, formula)
                  }
                } else {
                  val maybes = and(partEvaledPairs.map {
                    case (key_v, (key, value, value_v)) => E(Utils.maybe)(MapApply(newOut, key) === value)
                  }: _*)
                  Stream(ProgramFormula(newOut, Formula(Map(), Set(v.toVal), Set(), maybes)))
                }*/
              case fm: FiniteMap => // Raw replacement
                val (newFiniteMapKV) = (ListBuffer[Stream[(Expr, ProgramFormula)]]() /: partEvaledPairs) {
                  case (lb, (key_v, (key, value, value_v))) =>
                    if(!fm.pairs.exists(_._1 == key_v)) {
                      lb
                    } else {
                      val i = fm.pairs.lastIndexWhere(_._1 == key_v)
                      val newValue = fm.pairs(i)._2
                      lb += repair(program.subExpr(value), newValue).map(pf => (key, pf))
                    }
                }.toList
                for {solution <- inox.utils.StreamUtils.cartesianProduct(newFiniteMapKV)
                     (mapKeys, mapValuesFormula) = solution.unzip
                     mapValues = mapValuesFormula.map(_.program)
                     mapFormula = mapValuesFormula.map(_.formula)
                     formula = (Formula() /: mapFormula){ case (f, ff) => f combineWith ff }
                } yield {
                  ProgramFormula(FiniteMap(mapKeys.zip(mapValues), l.default, l.keyType, l.valueType), formula)
                }
              case _ => throw new Exception("Don't know what to do, not a Literal or a Variable: " + newOut)
            }

          }
        case lFun@Lambda(vd, body) =>  // Check for closures, i.e. free variables.
          val freeVars = exprOps.variablesOf(body).map(_.toVal) -- vd
          if(freeVars.isEmpty) {
            newOut match {
              case l: Lambda =>
                val freeVarsOfOut = exprOps.variablesOf(l)

                if(freeVarsOfOut.isEmpty) {
                  Stream(ProgramFormula(newOut, Formula()))
                } else
                for {maybeMapping <- obtainMapping(l, freeVarsOfOut, Map(), lFun)
                     constraint = and(maybeMapping.toSeq.map { case (k, v) => E(Utils.maybe)(k.toVariable === v) }: _*) /: Log.constraint
                } yield {
                  val isConstraintVariable = exprOps.variablesOf(constraint).map(_.toVal)
                  val variables = freeVarsOfOut.map(_.toVal)
                  val (constrainedVariables, unconstraintedVariables) = variables.partition(isConstraintVariable)
                  Log("Returning formula")
                  ProgramFormula(newOut, Formula(Map(), constrainedVariables, unconstraintedVariables, constraint))
                }
              case v: Variable =>
                Stream(ProgramFormula(newOut, Formula(Map(), Set(v.toVal), Set())))
              case _ => ???
            }
          }  else { // Closure
            if(exprOps.variablesOf(newOut) == freeVars) { // Same free variables, we just take the new out.
              Stream(ProgramFormula(newOut, Formula.maybeDefault(freeVars, currentValues)))
            } else
            // We need to determine the values of these free variables. We assume that the lambda kept the same shape.
            newOut match {
            case Lambda(vd2, expectedBody) =>
              val oldToFresh = vd.map{ v =>
                v -> ValDef(FreshIdentifier(v.id.name, true), v.tpe, v.flags)
              }.toMap
              val freshToOld = oldToFresh.map{ case (k, v) => v -> k.toVariable}
              val freshToValue = vd.map{ v =>
                oldToFresh(v) -> defaultValue(v.getType)
              }.toMap
              val bodyWithFreshVariables = exprOps.replaceFromSymbols(oldToFresh.mapValues(_.toVariable), body)
              val oldToValue = oldToFresh.mapValues(freshToValue)
              val variablesToAssign = program.formula.varsToAssign ++ oldToFresh.values

              val simplifiedExpectedBody = simplify(exprOps.replaceFromSymbols(oldToValue, expectedBody))
              Log(s"variablesToAssign: $variablesToAssign, oldToFresh = $oldToFresh")
              for {pf <- repair(ProgramFormula(bodyWithFreshVariables,
                Formula(freshToValue ++ freeVars.map(fv => fv -> currentValues(fv)).toMap, variablesToAssign)), simplifiedExpectedBody)
              } yield {
                  val ProgramFormula(newBody, f) = pf
                  Log(s"Going to test if lambda can be repaired using $newBody, $f, $freshToValue")
                  val newFreevarAssignments = freeVars.flatMap(fv => f.known.get(fv).map(res => fv -> res)).toMap
                  val newConstraint = f.unknownConstraints &<>& and(freshToValue.toSeq.map{ case (k, v) => k.toVariable === v}: _*)
                  Log(s"Returning lambda using $newBody, $f, $freshToValue, \n$newFreevarAssignments")
                  val fullNewBody = exprOps.replaceFromSymbols(freshToOld, newBody)
                  //val newFormula = f combineWith

                  ProgramFormula(Lambda(vd, fullNewBody): Expr,
                    Formula(newFreevarAssignments, f.varsToAssign -- vd2,
                      f.unchanged -- vd2 -- freshToValue.keys, newConstraint)) /: Log
                }
            case v: Variable =>
              Stream(ProgramFormula(v, Formula(Map(), Set(), Set(v.toVal))))
            case _ => ???
            }
          }

        // Variables are assigned the given value.
        case v@Variable(id, tpe, flags) =>
          newOut match {
            case v2: Variable =>
              Stream(ProgramFormula(v, Formula(Map(), Set(v.toVal, v2.toVal), Set(), v2 === v)))/* && E(Utils.maybe)(v2 === currentValues(v.toVal))))*/
            /*case f: FiniteMap => // Special case because we should only propagate changes in the map itself.
              functionValue match {
                case fm@FiniteMap(pairs, default, kt, vt) =>
                  val newFormula = (Formula() /: f.pairs) { case (formula, (key, value)) =>
                    val i = fm.pairs.lastIndexWhere(_._1 == key)
                    if(i == -1) { // It has been inserted
                      println(s"$key did not appear in $fm, adding a constraint")
                      formula combineWith Formula(Map(), exprOps.variablesOf(value).map(_.toVal) + v.toVal, Set(),
                        MapApply(v, key) === value
                      )
                    } else {
                      val previousValue = fm.pairs(i)._2
                      if(previousValue != value) { // A variable has been put there.
                        println(s"$previousValue != $value so we add it to the formula, for key $key")
                        formula combineWith Formula(Map(), exprOps.variablesOf(value).map(_.toVal) + v.toVal, Set(),
                          MapApply(v, key) === value
                        )
                      } else formula
                    }
                  }
                  Stream(ProgramFormula(v, newFormula))
                case _ => throw new Exception(s"Value not a Map: $functionValue")
              }*/
            case _ =>
              /*if(currentValues(v.toVal) == newOut) { // TODO: Evaluate newOut
                Stream(ProgramFormula(v, Formula.maybeDefault(Set(v.toVal), Map(v.toVal -> newOut))))
              } else {*/
                val varsOfNewOut = exprOps.variablesOf(newOut).map(_.toVal)
                Stream(ProgramFormula(v, Formula(Map(), Set(v.toVal) ++ varsOfNewOut, Set(), v === newOut)))
              //}
          }

        case Let(vd, expr, body) =>
          repair(ProgramFormula(Application(Lambda(Seq(vd), body), Seq(expr)), program.formula), newOut).map {
            case ProgramFormula(Application(Lambda(Seq(vd), body), Seq(expr)), f) =>
              ProgramFormula(Let(vd, expr, body), f)
            case e  => throw new Exception(s"Don't know how to get a Let back from $e")
          }

        case StringConcat(expr1, expr2) =>
          ifEmpty(for(pf <- repair(program.copy(program = FunctionInvocation(StringConcatReverser.identifier, Nil,
            Seq(expr1, expr2))), newOut)) yield {
            pf match {
              case ProgramFormula(FunctionInvocation(StringConcatReverser.identifier, Nil, Seq(x, y)), f) =>
                ProgramFormula(StringConcat(x, y), f)
            }
          }){
            val constraint = newOut === function
            Stream(ProgramFormula(function,
              Formula(Map(), exprOps.variablesOf(constraint).map(_.toVal), Set(), constraint)))
          }

        case ADT(ADTType(tp, tpArgs), argsIn) =>
          newOut match {
            case v: Variable => Stream(ProgramFormula(v, Formula(Map(), Set(), Set(v.toVal))))
            case ADT(ADTType(tp2, tpArgs2), argsOut) if tp2 == tp && tpArgs2 == tpArgs && functionValue != newOut => // Same type ! Maybe the arguments will change or move.
              val seqOfStreamSolutions = argsIn.zip(argsOut).map { case (aFun, aVal) =>
                repair(ProgramFormula(aFun, program.formula), aVal)
              }
              val streamOfSeqSolutions = inox.utils.StreamUtils.cartesianProduct(seqOfStreamSolutions)
              for {seq <- streamOfSeqSolutions
                   _ = Log(s"combineResults($seq, $currentValues)")
                   (newArgs, assignments) = combineResults(seq, currentValues)
              } yield {
                ProgramFormula(ADT(ADTType(tp2, tpArgs2), newArgs), assignments)
              }
            case ADT(ADTType(tp2, tpArgs2), args2) => Stream.empty // Wrapping already handled.

            case a => // Another value in the type hierarchy. But Maybe sub-trees are shared !
              throw new Exception(s"Don't know how to handle this case : $a is supposed to be put in place of a ${tp}")
          }

        case as@ADTSelector(adt, selector) =>
          val originalAdtValue = evalWithCache(letm(currentValues) in adt).asInstanceOf[ADT]
          val constructor = as.constructor.get
          val fields = constructor.fields
          val index = as.selectorIndex
          val vds = fields.map{ fd => ValDef(FreshIdentifier("x", true), fd.getType, Set())}
          val constraints = vds.zipWithIndex map {
            case (vd, i) => if(i == index) {
              vd.toVariable === newOut
            } else {
              E(Utils.maybe)(vd.toVariable === originalAdtValue.args(i))
            }
          }

          for{ pf <- repair(program.subExpr(adt),
            ADT(ADTType(constructor.id, constructor.tps), vds.map(_.toVariable))) } yield {
            pf.wrap(x => ADTSelector(x, selector)) combineWith Formula(
              varsToAssign = vds.toSet,
              unknownConstraints = and(constraints : _*))
          }

        case MapApply(map, key) => // Variant of ADT selection.
          val map_v = evalWithCache(letm(currentValues) in map).asInstanceOf[FiniteMap] //originalAdtValue
          val key_v = evalWithCache(letm(currentValues) in key)

          val defaultValue = map_v.default

          val vds = map_v.pairs.map{ case (k, v) => (k, ValDef(FreshIdentifier("x", true), map_v.valueType, Set()))}
          var found = false
          val constraints = (vds map {
            case (k, vd) => if(k == key_v) {
              found = true
              vd.toVariable === newOut
            } else {
              E(Utils.maybe)(vd.toVariable === evalWithCache(MapApply(map_v, k)))
            }
          })
          val finiteMapRepair = if (!found) { // We should not change the default, rather add a new entry.
            FiniteMap(vds.map{x => (x._1, x._2.toVariable)} :+ (key_v -> newOut)
              , map_v.default, map_v.keyType, map_v.valueType)
          } else {
            FiniteMap(vds.map{x => (x._1, x._2.toVariable)}, map_v.default, map_v.keyType, map_v.valueType)
          }

          for{ pf <- repair(program.subExpr(map), finiteMapRepair) } yield {
            pf.wrap(x => MapApply(x, key)) combineWith Formula(
              varsToAssign = vds.map(_._2).toSet,
              unknownConstraints = and(constraints : _*))
          }

        case m@Application(lambdaExpr, arguments) =>
          val originalValue = (lambdaExpr match {
            case v: Variable => currentValues.getOrElse(v.toVal, evalWithCache(letm(currentValues) in v))
            case l => evalWithCache(letm(currentValues) in l) // Should be a lambda
          }) =: Log.Original_Value
          originalValue match {
            case l@Lambda(argNames, body) =>
              val freshArgsNames = argNames.map(vd => ValDef(FreshIdentifier(vd.id.name, true), vd.tpe, vd.flags))
              val freshBody = exprOps.replaceFromSymbols(argNames.zip(freshArgsNames.map(_.toVariable)).toMap, body)
              val oldToFresh = argNames.zip(freshArgsNames).toMap
              val freshToOld = freshArgsNames.zip(argNames.map(_.toVariable)).toMap
              val argumentValues = argNames.zip(arguments.map(arg => evalWithCache(letm(currentValues) in arg))).toMap
              val freshArgumentValues = argumentValues.map{ case (k,v) => oldToFresh(k) -> v}
              val freshFormula = Formula(freshArgumentValues, freshArgsNames.toSet)
              for {pf <-
                     repair(ProgramFormula(freshBody, freshFormula).wrappingEnabled, newOut)  /::
                       Log.prefix(s"From repair$stackLevel'(\n  $freshBody,\n  $freshFormula,\n  $newOut), recovered:\n")
                   ProgramFormula(newBodyFresh, newBodyFreshFormula) = pf
                   newBody = exprOps.replaceFromSymbols(freshToOld, newBodyFresh)
                   isSameBody = (newBody == body)              /: Log.isSameBody
                   args <-
                     combineArguments(program combineWith newBodyFreshFormula,
                       arguments.zip(freshArgsNames).map { case (arg, v) =>
                      val expected = newBodyFreshFormula.getOrElse(v, argumentValues(freshToOld(v).toVal))
                      (arg, expected)
                     })
                   (newArguments, newArgumentsFormula) = args
                   newLambda = if (isSameBody) l else Lambda(argNames, newBody)
                   pfLambda <- lambdaExpr match {
                     case v: Variable => Stream(ProgramFormula(v, (
                       if(isSameBody) Formula.maybeDefault(Set(v.toVal), currentValues) else
                         Formula(Map(v.toVal -> newLambda), Set(v.toVal)))))
                     case l => repair(ProgramFormula(l, program.formula), newLambda)
                   }
                   ProgramFormula(newAppliee, lambdaRepairFormula) = pfLambda
                   finalApplication = Application(newAppliee, newArguments)           /: Log.prefix("finalApplication")
              } yield {
                val combinedFormula = newBodyFreshFormula combineWith lambdaRepairFormula combineWith newArgumentsFormula
                Log.prefix("[return] ")  :=
                ProgramFormula(finalApplication: Expr, combinedFormula)
              }
            case _ => throw new Exception(s"Don't know how to handle this case : $m of type ${m.getClass.getName}")
          }

        case funInv@FunctionInvocation(f, tpes, args) =>
          // We need to reverse the invocation arguments.
          reversions.get(f) match {
            case None => Stream.empty  /: Log.prefix(s"No function $f reversible for : $funInv.\nIt evaluates to:\n$functionValue.")
            case Some(reverser) =>
              val argsValue = args.map(arg => evalWithCache(letm(currentValues) in arg))
              val lenseResult = reverser.put(tpes)(argsValue, newOut)
              for{l <- lenseResult; (newArgsValues, newForm) = l
                  a <- combineArguments(program, args.zip(newArgsValues))
                  (newArguments, newArgumentsFormula) = a
              } yield {
                val formula = newForm combineWith newArgumentsFormula
                ProgramFormula(FunctionInvocation(f, tpes, newArguments), formula)
              }
          }
        case anyExpr =>
          Log(s"Don't know how to handle this case : $anyExpr of type ${anyExpr.getClass.getName},\nIt evaluates to:\n$functionValue.")
          Stream.empty
      }
    } #::: {Log(s"Finished repair$stackLevel"); Stream.empty[ProgramFormula]}  /:: Log.prefix(s"@return for repair$stackLevel(\n  $program\n, $newOut):\n~>")
  }

  /** Given a sequence of (arguments expression, expectedValue),
      returns the cartesian product of all argument programs and solutions. */
  private def combineArguments(pf: ProgramFormula,
      arguments: Seq[(Expr, Expr)])(implicit symbols: Symbols, cache: Cache): Stream[(Seq[Expr], Formula)] = {
    Log(s"combining arguments for $pf")
    val argumentsReversed = arguments.map { case (arg, expected) =>
      Log(s" repairing argument $arg should equal $expected")
      repair(ProgramFormula(arg, pf.formula), expected)
    }
    for ( r <- inox.utils.StreamUtils.cartesianProduct(argumentsReversed)) yield {
     (r.map(_.program),
       (Formula() /: r) { case (f, pfr) => f combineWith pfr.formula })//r.map(_.formula))
    }
  }

  // Given a ProgramFormula for each of the fields, returns a list of expr and a single formulas
  private def combineResults(seq: List[ProgramFormula], currentValues: Map[ValDef,Expr])
            (implicit symbols: Symbols, cache: Cache): (List[Expr], Formula) = {
    val (lb, f) = ((ListBuffer[Expr](), Formula()) /: seq) {
      case total@((ls, f1), (ProgramFormula(l, f2))) =>
        (ls += l, f1 combineWith f2)
    }
    (lb.toList, f)
  }


  /** Simple function returning true if the given expression is a value. */
  @inline private def isValue(e: Expr) = {
    !exprOps.exists{
      case _: Lambda => false
      case _: Literal[_] => false
      case ADT(_, _) => false
      case _: FiniteMap => false
      case _: FiniteBag => false
      case _: FiniteSet => false
      case _ => true
    }(e)
  }

  /* Example:
    function = v
    functionValue = Element("b", List(), List(), List())
    newOut = Element("div", List(Element("b", List(), List(), List())), List(), List())
    result: Element("div", List(v), List(), List())
  * */
  private def maybeWrap(program: ProgramFormula, newOut: Expr, functionValue: Expr)(implicit symbols: Symbols): Stream[ProgramFormula] = {
    val function = program.program
    if(functionValue == newOut) return Stream.empty[ProgramFormula] // Value returned in maybeUnwrap

    val containsFunctionValue = exprOps.exists {
      case t if t == functionValue => true
      case _ => false
    } _

    // Checks if the old value is inside the new value, in which case we add a wrapper.
    if (containsFunctionValue(newOut)) {
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
      if(canWrap) {
        // We wrap the computation of functionValue with ADT construction

        val newFunction = exprOps.postMap {
          case t if t == functionValue => Some(function)
          case _ => None
        }(newOut)
        val variables = program.formula.varsToAssign ++ program.freeVars
        val constraintExpression = program.formula.unknownConstraints
        val constraintFreeVariables = exprOps.variablesOf(constraintExpression).map(_.toVal)

        val (constraining, unconstrained) = variables.partition(constraintFreeVariables)

        Stream(ProgramFormula(newFunction,
          Formula(known = Map(), constraining, unconstrained, unknownConstraints = program.formula.unknownConstraints
          )))
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
  private def maybeUnwrap(program: ProgramFormula, newOut: Expr, functionValue: Expr)(implicit symbols: Symbols): Stream[ProgramFormula] = {
    val function = program.program
    if(functionValue == newOut) {
      Log("@return unwrapped")
      return Stream(program.copy(formula =
        Formula(known = Map(), Set(), program.freeVars)
        ))
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
          maybeUnwrap(ProgramFormula(args(i), program.formula), newOut, arg)
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
    val function = program.program
    if(functionValue == newOut) {
      Log("@return unwrapped")
      return Stream(program.copy(formula = Formula(known = Map(), varsToAssign = Set(), program.freeVars)))
    }
    newOut match {
      case StringLiteral(s) =>
        function match {
          case StringLiteral(_) => Stream.empty // We can always replace the StringLiteral later
          //case StringConcat(_, _) => Stream.empty // We can always add the constant to a sub-expression, to avoid duplicate programs
          case _ =>
            functionValue match {
              case StringLiteral(t) =>((
                if(s.startsWith(t)) {
                  Stream(ProgramFormula(StringConcat(function, StringLiteral(s.substring(t.length))), Formula(known = Map(), varsToAssign = Set(), program.freeVars)))
                } else Stream.empty) #::: (
                if(s.endsWith(t)) {
                  Stream(ProgramFormula(StringConcat(StringLiteral(s.substring(0, s.length - t.length)), function), Formula(known = Map(), varsToAssign = Set(), program.freeVars)))
                } else Stream.empty
                )) /:: Log.prefix("@return wrapped: ")
              case _ => Stream.empty
            }
        }
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
