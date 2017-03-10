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
  case class Formula(known: Map[ValDef, Expr], unknownConstraints: Expr)(implicit symbols: Symbols) {
    // The assignments and the formula containing the other expressions.
    def determinizeAll(freeVariables: List[Variable]): Stream[Map[ValDef, Expr]] = {
      if(freeVariables.isEmpty) return Stream(Map())
      unknownConstraints match {
        case BooleanLiteral(true) => Stream(freeVariables.map(fv => fv.toVal -> known(fv.toVal)).toMap)
        case BooleanLiteral(false) => Stream.empty
        case _ =>
          val input = Variable(FreshIdentifier("input"), tupleTypeWrap(freeVariables.map(_.getType)), Set())
          val constraint = InoxConstraint(input === tupleWrap(freeVariables) && unknownConstraints)
          constraint.toStreamOfInoxExpr(input).map {
            case Tuple(args) => freeVariables.zip(args).map{ case (fv: Variable, expr: Expr) => fv.toVal -> expr }.toMap
            case e if freeVariables.length == 1 =>
              Map(freeVariables.head.toVal -> e)
          }
      }
    }
  }

  import Utils._
  import Constrainable._
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
  def put[A: Constrainable](out: A, prevOut: Option[OutExpr], modif: Option[ModificationSteps], prevIn: Option[(InoxProgram, FunctionEntry)]): Iterable[(InoxProgram, FunctionEntry)] = {
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
    implicit val cache = new mutable.HashMap[Expr, Expr]
    for {(newOutExpr, f) <- repair(prevBody, Map(), outExpr)
         //_ = println("Remaining formula: " + f)
         //_ = println("Remaining expression: " + newOutExpr)
         assignments <- f.determinizeAll(exprOps.variablesOf(newOutExpr).toList)
         //_ = println("Found assignments: " + assignments)
         finalNewOutExpr = exprOps.replaceFromSymbols(assignments, newOutExpr)
         //_ = println("Final  expression: " + finalNewOutExpr)
         newFunDef = mkFunDef(newMain)()(stp => (Seq(), prevFunction.returnType, _ => finalNewOutExpr))
         newProgram = InoxProgram(context, symbols.withFunctions(Seq(newFunDef)))
    } yield (newProgram, newMain)
  }

  /** Eval function. Uses a cache normally*/
  def evalWithCache(expr: Expr)(implicit cache: Cache, symbols: Symbols) = cache.getOrElseUpdate(expr, {
    val funDef = mkFunDef(FreshIdentifier("main"))()(stp => (Seq(), expr.getType, _ => expr))
    val prog = InoxProgram(context, symbols)
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

  object StringConcats {
    def unapply(s: Expr): Some[Seq[Expr]] = s match {
      case StringConcat(a, b) => Some(this.unapply(a).get ++ this.unapply(b).get)
      case x => Some(Seq(x))
    }
  }

  @inline def castOrFail[A, B <: A](a: A): B =
    a.asInstanceOf[B]

  @inline def asStr(e: Expr): String = castOrFail[Expr, StringLiteral](e).value
  
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
    * @param newOut Either a literal value that should be produced by function, or a variable,
    *               in which case the result will have in the formula a constraint over this variable,
    *               Or a let-expression to denote a clone-and-paste.
    * @return A set of possible expressions, along with a set of possible assignments to input variables.
    **/
  def repair(function: Expr, currentValues: Map[ValDef, Expr], newOut: Expr)
            (implicit symbols: Symbols, cache: Cache): Stream[(Expr, Formula)] = {
    //println(s"\n@solving ${currentValues.map{ case (k, v) => s"val ${k.id} = $v\n"}.mkString("")}$function = $newOut")
    if(function == newOut) return { //println("@return original");
      Stream((function, Formula(Map[ValDef, Expr](), BooleanLiteral(true))))
    }

    lazy val functionValue = evalWithCache(letm(currentValues) in function) // TODO: Optimize this ?

    {
      function.getType match {
        case a: ADTType if !newOut.isInstanceOf[Variable] =>
          function match {
            case l: Let => Stream.empty[(Expr, Formula)] // No need to wrap a let expression, we can always do this later. Indeed,
              //f{val x = A; B} = {val x = A; f(B)}
            case _ =>
              maybeWrap(function, newOut, functionValue) #::: maybeUnwrap(function, newOut, functionValue)
          }
        case _ => Stream.empty[(Expr, Formula)]
      }
    } #::: {
      val res: Stream[(Expr, Formula)] = function match {
        // Values (including lambdas) should be immediately replaced by the new value
        case l: Literal[_] =>
          newOut match {
            case l: Literal[_] => // Raw replacement
              Stream((newOut, Formula(Map(), BooleanLiteral(true))))
            case v: Variable => // Replacement with the variable newOut, with a maybe clause.
              Stream((newOut, Formula(Map(), E(Common.maybe)(v === l))))
            case l@Let(cloned: ValDef, _, _) =>
              Stream((newOut, Formula(Map(), BooleanLiteral(true))))
            case _ => throw new Exception("Don't know what to do, not a Literal, a Variable, or a let: "+newOut)
          }
        case lFun@Lambda(vd, body) =>  // Check for closures, i.e. free variables.
          val freeVars = exprOps.variablesOf(body).map(_.toVal) -- vd
          if(freeVars.isEmpty) {
            newOut match {
              case l: Lambda =>
                Stream((newOut, Formula(Map(), BooleanLiteral(true))))
              case v: Variable =>
                Stream((newOut, Formula(Map(), E(Common.maybe)(v === lFun))))
              case _ => ???
            }
          }  else { // Closure
            // We need to determine the values of these free variables.
            newOut match {
              case Lambda(vd2, body2) =>
              val dummyInputs = vd.map{ v =>
                v -> defaultValue(v.getType)
              }.toMap
              for{(newBody, Formula(newAssignments, constraint)) <-
                  repair(body, dummyInputs ++ freeVars.map(fv => fv -> currentValues(fv)).toMap, body2)
                newFreevarAssignments = freeVars.flatMap(fv => newAssignments.get(fv).map(res => fv -> res)).toMap }
                yield {
                  (Lambda(vd, newBody): Expr, Formula(newFreevarAssignments, constraint))
                }
              case v: Variable => ???
              case _ => ???
            }
          }

        // Variables are assigned the given value.
        case v@Variable(id, tpe, flags) =>
          newOut match {
            case v2: Variable =>
              Stream((v, Formula(Map(), v2 === v)))
            case _ =>
              Stream((v, Formula(Map(v.toVal -> newOut), BooleanLiteral(true))))
          }

        // Let expressions eval their variable, reverse their body and then their assigning expression
        // It comes from the fact that
        // let x = b in c[x]    is equivalent to      Application((\x. c[x]), (b))
        // In theory with rewriting it could be dropped, but we still do inline it for now.
        case Let(vd@ValDef(id, tpe, flags), expr, body) =>
          val currentVdValue = evalWithCache(letm(currentValues) in expr)

          for { (newBody, Formula(newAssignment, constraint)) <-
                 repair(body, currentValues + (vd -> currentVdValue), newOut) // Later: Change assignments to constraints
               // If newAssignment does not contain vd, it means that newBody is a variable present in constraint.
               isAssigned = newAssignment.contains(vd)
               newValValue = (if(isAssigned) newAssignment(vd) else ValDef(FreshIdentifier("t", true), tpe, Set()).toVariable)
               (newExpr, Formula(newAssignment2, constraint2)) <- repair(expr, currentValues, newValValue)
               newFunction = Let(vd, newExpr, newBody)
               finalAssignments = (newAssignment ++ newAssignment2) - vd
          } yield {
            if(isAssigned) {
              (newFunction, Formula(finalAssignments, constraint2 &<>& constraint))
            } else {
              (newFunction, Formula(finalAssignments, constraint2 &<>& constraint && newValValue === vd.toVariable))
            }
          }

        case StringConcat(expr1, expr2) =>
          lazy val leftValue = evalWithCache(letm(currentValues) in expr1)
          lazy val rightValue = evalWithCache(letm(currentValues) in expr2)
          lazy val finalValue = asStr(leftValue) + asStr(rightValue)

          def defaultCase = {
            val left = ValDef(FreshIdentifier("left"), StringType, Set())
            val right = ValDef(FreshIdentifier("right"), StringType, Set())

            val leftRepair = repair(expr1, currentValues, left.toVariable)
            val rightRepair = repair(expr2, currentValues, right.toVariable)

            val bothRepair = inox.utils.StreamUtils.cartesianProduct(leftRepair, rightRepair)

            bothRepair.map { case ((leftExpr, f1@Formula(mp1, cs1)), (rightExpr, f2@Formula(mp2, cs2))) =>
              val newCs = cs1 &<>& cs2 &<>& newOut === StringConcat(left.toVariable, right.toVariable)
              (StringConcat(leftExpr, rightExpr), Formula(mp1 ++ mp2, newCs))
            }
          }

          // Prioritize changes that touch only one of the two expressions.
          newOut match{
            case StringLiteral(s) =>
              (leftValue match {
                case StringLiteral(lv) =>
                if(s.startsWith(lv)) {
                  val right = ValDef(FreshIdentifier("right"), StringType, Set())
                  val rightRepair = repair(expr2, currentValues, StringLiteral(s.substring(lv.length)))
                  rightRepair.map { case (rightExpr, f) =>
                    (StringConcat(expr1, rightExpr), f)
                  }
                } else Stream.empty
                case _  => Stream.empty }) #::: (
                rightValue match {
                  case StringLiteral(rv) =>
                  if(s.endsWith(rv)) {
                    val left = ValDef(FreshIdentifier("left"), StringType, Set())
                    val leftRepair = repair(expr1, currentValues, StringLiteral(s.substring(0, s.length - rv.length)))
                    leftRepair.map { case (leftExpr, f) =>
                      (StringConcat(leftExpr, expr2), f)
                    }
                  } else Stream.empty
                case _  => Stream.empty
                }
              ) #::: defaultCase
            case newOut: Variable => defaultCase

            case l@Let(vd, value, newbody) =>
              /* Copy and paste, insertion, replacement:
              *  => A single let(v, newText, newbody) with a single occurrence of v in newbody
              *  Clone and paste
              *  => A double let(clone, oldText, let(paste, clone, newbody)) with two occurrences of clone in newbody
              *  Cut and paste
              *  => A double let(cut, "", let(paste, clone, newbody)) with one occurrences of paste in newbody
              *  Delete
              *  => A single let(delete, "", newbody) with a single occurrence of delete in newbody
              **/
              ???

            case _ => throw new Exception(s"Don't know how to handle $newOut")
          }

        case ADT(ADTType(tp, tpArgs), args) =>
          newOut match {
            case v: Variable => Stream((v, Formula(Map(), v === function))) // TODO: Might be too restrictive?
            case ADT(ADTType(tp2, tpArgs2), args2) if tp2 == tp && tpArgs2 == tpArgs => // Same type ! Maybe the arguments will change or move.
              if (args.length == 0) { // Nil-like
                  Stream((newOut, Formula(Map(), BooleanLiteral(true))))
              } else {
                // Now args.length > 0
                val adt = castOrFail[ADTDefinition, ADTConstructor](symbols.adts(tp))
                val tadt = adt.typed(tpArgs)
                val seqOfStreamSolutions = (args.zip(args2).zip(tadt.fields).map { case ((aFun, aVal), avd) =>
                  repair(aFun, currentValues, aVal).map(
                    (_, avd, () => evalWithCache(letm(currentValues) in aFun)))
                })
                val streamOfSeqSolutions = inox.utils.StreamUtils.cartesianProduct(seqOfStreamSolutions)
                for {seq <- streamOfSeqSolutions
                     reduced = combineResults(seq, currentValues)
                     newArgs = reduced._1.reverse
                     assignments = reduced._2
                } yield {
                  (ADT(ADTType(tp2, tpArgs2), newArgs), assignments)
                }
              }
            case ADT(ADTType(tp2, tpArgs2), args2) => Stream.empty // Wrapping already handled.

            case a => // Another value in the type hierarchy. But Maybe sub-trees are shared !
              throw new Exception(s"Don't know how to handle this case : $a is supposed to be put in place of a ${tp}")
          }

        case m@Application(lambdaExpr, arguments) =>
          val originalValue = lambdaExpr match {
            case v: Variable => currentValues.getOrElse(v.toVal, evalWithCache(letm(currentValues) in v))
            case l => evalWithCache(letm(currentValues) in l) // Should be a lambda
          }
          originalValue match {
            case l@Lambda(argNames, body) =>
              val argumentValues = argNames.zip(arguments.map(arg => evalWithCache(letm(currentValues) in arg))).toMap
              for {(newBody, Formula(assignments, constraint)) <-
                     repair(body, argumentValues, newOut)
                   argumentsReversed = arguments.zip(argNames).map { case (arg, v) =>
                     repair(arg, currentValues, assignments.getOrElse(v, argumentValues(v)))
                   }.zipWithIndex.map{ case (x, i) =>
                     if(x.isEmpty) Stream((argumentValues(argNames(i)), Formula(Map(), BooleanLiteral(true)))) else x
                   }
                   newArgumentsAssignments <- inox.utils.StreamUtils.cartesianProduct(argumentsReversed)
                   newArguments = newArgumentsAssignments.map(_._1)
                   isSameBody = newBody == body
                   newLambda = if (isSameBody) l else Lambda(argNames, newBody)
                   (newAppliee, Formula(assignments2, cs)) <- lambdaExpr match {
                     case v: Variable => Stream(v -> (
                       if(isSameBody) Formula(Map(), BooleanLiteral(true)) else
                         Formula(Map(v.toVal -> newLambda), BooleanLiteral(true))))
                     case l: Lambda => repair(lambdaExpr, currentValues, newLambda)
                   }
                   finalApplication = Application(newAppliee, newArguments)
                   newAssignments = Map[ValDef, Expr]() ++ assignments2 ++
                     newArgumentsAssignments.flatMap(_._2.known.toList) // TODO: Deal with variable value merging like above.
              } yield {
                (finalApplication: Expr, Formula(newAssignments, constraint &<>& cs)) // TODO: Check order.
              }
            case _ => throw new Exception(s"Don't know how to handle this case : $m of type ${m.getClass.getName}")
          }

        case funInv@FunctionInvocation(f, tpes, args) =>
          // We need to reverse the invocation arguments.
          reversions.get(f) match {
            case None =>
              println(s"No function $f reversible for : $funInv.\nIt evaluates to:\n$functionValue.")
              Stream.empty
            case Some(reverser) =>
              reverser(tpes)(args.map(arg => evalWithCache(letm(currentValues) in arg)), newOut).map{ case (seqArgs, formula) =>
                (FunctionInvocation(f, tpes, seqArgs), formula)
              }
          }

        case anyExpr =>
          println(s"Don't know how to handle this case : $anyExpr of type ${anyExpr.getClass.getName},\nIt evaluates to:\n$functionValue.")
          Stream.empty
      }
      res
    }
  }

  val reversions = Map[Identifier, Reverser](
    FilterReverser.mapping
  )

  abstract class Reverser {
    def identifier: Identifier
    def mapping = identifier -> this
    def apply(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: Expr)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[Expr], Formula)]
  }

  case object FilterReverser extends Reverser with FilterLike[Expr] { // TODO: Incorporate filterRev as part of the sources.
    val identifier = Utils.filter
    def unwrapList(e: Expr): List[Expr] = e match {
      case ADT(ADTType(Utils.cons, tps), Seq(head, tail)) =>
        head :: unwrapList(tail)
      case ADT(ADTType(Utils.nil, tps), Seq()) =>
        Nil
    }
    def wrapList(e: List[Expr], tps: Seq[Type]): Expr = e match {
      case head :: tail =>
        ADT(ADTType(Utils.cons, tps), Seq(head, wrapList(tail, tps)))
      case Nil =>
        ADT(ADTType(Utils.nil, tps), Seq())
    }
    def apply(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: Expr)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[Expr], Formula)] = {
      val lambda = originalArgsValues.tail.head
      val originalInput = originalArgsValues.head
      //println(s"Reversing $originalArgs: $originalOutput => $newOutput")
      filterRev(unwrapList(originalInput), (expr: Expr) => evalWithCache(Application(lambda, Seq(expr))) == BooleanLiteral(true), unwrapList(newOutput)).map{ (e: List[Expr]) =>
        println(s"First solution: $e")
        (Seq(wrapList(e, tpes), lambda), Formula(Map(), BooleanLiteral(true)))
      }
    }
  }


  private def combineResults(seq: List[((Expr, Formula), ValDef, () => inox.trees.Expr)], currentValues: Map[ValDef,Expr])
            (implicit symbols: Symbols, cache: Cache) =
    ((List[Expr](), Formula(Map[ValDef, Expr](), BooleanLiteral(true))) /: seq) {
    case ((ls, Formula(mm, cs1)), ((l, Formula(m, cs2)), field, recompute)) =>
      if ((mm.keys.toSet intersect m.keys.toSet).nonEmpty && {
        // Compare new assignment with the original value.
        val realValue = currentValues(m.keys.head)
        realValue == m(m.keys.head)
      }) {
        // The value did not change ! We shall not put it in the assignment map.
        (l :: ls, Formula(mm, cs1))
      } else (l :: ls, Formula(mm ++ m, cs1 &<>& cs2))
  }

  /* Example:
    function = v
    functionValue = Element("b", List(), List(), List())
    newOut = Element("div", List(Element("b", List(), List(), List())), List(), List())
    result: Element("div", List(v), List(), List())
  * */
  private def maybeWrap(function: Expr, newOut: Expr, functionValue: Expr)(implicit symbols: Symbols): Stream[(Expr, Formula)] = {
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

      Stream((newFunction, Formula(Map(), BooleanLiteral(true))))
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
  private def maybeUnwrap(function: Expr, newOut: Expr, functionValue: Expr)(implicit symbols: Symbols): Stream[(Expr, Formula)] = {
    if(functionValue == newOut) return Stream((function, Formula(Map(), BooleanLiteral(true))))

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
