package perfect.core

import scala.collection.mutable.ListBuffer

/**
  * Created by Mikael on 06/05/2017.
  */
trait ContExps { self: ProgramUpdater =>
  trait EvalContExpCommand {
    def unapply(e: Exp): Option[Exp]
  }

  trait ContExpCommand {
    def Eval: EvalContExpCommand
    def merge(a1: Exp, a2: Exp): Option[(Exp, Seq[(Var, KnownValue)])]
  }

  def commands: List[ContExpCommand]

  sealed trait KnownValue {
    def getValue: Option[Exp]
    def getConstraint(k: Var): Exp
    def map(f: Exp => Exp): KnownValue
    def exists(f: Exp => Boolean): Boolean = getValue.exists(x => f(x))
  }
  case class StrongValue(e: Exp) extends KnownValue {
    def getValue = Some(e)
    def getConstraint(k: Var) = k === e
    def map(f: Exp => Exp): StrongValue = {
      StrongValue(f(e))
    }
  }
  case class OriginalValue(e: Exp) extends KnownValue {
    def getValue = Some(e)
    def getConstraint(k: Var) = Originally(k === e)
    def map(f: Exp => Exp): OriginalValue = {
      OriginalValue(f(e))
    }
  }
  case class InsertVariable(e: Exp) extends KnownValue {
    def getValue = Some(e)
    def getConstraint(k: Var) = k === e //throw new Exception("[Internal error] tried to get a constraint on an inserted variable")
    def map(f: Exp => Exp): InsertVariable = {
      InsertVariable(f(e))
    }
  }
  case object AllValues extends KnownValue {
    def getValue = None
    def getConstraint(k: Var) = ExpTrue
    def map(f: Exp => Exp): AllValues.type = this
  } // Universally quantified variables.

  object StrongOrOriginal {
    def unapply(e: KnownValue): Option[(Exp, Exp => KnownValue)] = e match {
      case StrongValue(e) => Some((e, (StrongValue(_))))
      case OriginalValue(e) => Some((e, (OriginalValue(_))))
      case AllValues => None
      case InsertVariable(_) => None
    }
  }

  /** A Context builder */
  object Cont {
    /** A deterministic constructor for Cont */
    def apply(ve: (Var, KnownValue)): Cont = Cont(Map(ve))

    def apply(formulas: Iterable[Cont])(implicit symbols: Symbols): Cont = {
      (Cont() /: formulas)(_ combineWith _)
    }

    def inlineSimpleConts(e: Cont): Cont = {
      def evalExprIfNeeded(e: Exp): Option[Exp] =
        commands.view.map{
          cpf => cpf.Eval.unapply(e)
        }.find(_.nonEmpty).flatten
      val result = e.known.map{
        case vso@(v, so@StrongOrOriginal(e, builder)) =>
          evalExprIfNeeded(e).map(v->builder(_)).getOrElse(vso)
        case m => m
      }
      Cont(result, postMap(evalExprIfNeeded)(e.constraints))
    }
  }

  /** Previously 'Formula'*/
  case class Cont(known: Map[Var, KnownValue] = Map(), constraints: Exp = ExpTrue) {
    import Cont._
    // Can contain middle free variables.
    lazy val varsToAssign: Set[Var] = known.keySet ++ freeVariables(constraints)

    lazy val assignmentsAsOriginals: Cont = {
      Cont(known.map{ case (k, StrongValue(e)) => (k, OriginalValue(e)) case kv => kv})
    }

    // A list of partial assignments if there is no further constraints.
    lazy val partialAssignments: Option[(Exp => Exp, List[(Var, KnownValue)])] = {
      def rec(constraints: Seq[(Var, KnownValue)], seen: Set[Var]): (Exp => Exp, List[(Var, KnownValue)]) = {
        if(constraints == Nil) return ((x: Exp) => x, Nil)
        // Possibility to build all assignments in one shot.
        val (sNewF, newSeen, remaining) = ((None: Option[Exp => Exp], seen, ListBuffer[(Var, KnownValue)]()) /: constraints) {
          case ((optF, seen, remaining), equ@(v, StrongOrOriginal(e, _))) if (freeVariables(e) -- seen).isEmpty =>
            optF match {
              case None => (Some((x: Exp) => Assign(v, e, x)), seen + v, remaining)
              case Some(f) => (Some((x: Exp) => f(Assign(v, e, x))), seen + v, remaining)
            }
          case ((optF, seen, remaining), equ) =>
            (optF, seen, remaining += equ)
        }
        val newF = sNewF.getOrElse((x: Exp) => x)
        if(remaining.length == 0 || newSeen.size == seen.size) { // no progress
          (newF, remaining.toList)
        } else {
          val (rf, remaining2) = rec(remaining, newSeen)
          ((x: Exp) => newF(rf(x)), remaining2)
        }
      }
      if(constraints != ExpTrue) None else {
        Some(rec(known.toSeq, Set()))
      }
    }

    /** If the constraints are complete, i.e. all variables can be defined, then we can generate a let-wrapper. */
    lazy val assignments: Option[Exp => Exp] = { // We know that variables appear only once in the lhs of the seq
      partialAssignments.flatMap{
        case (f, Nil) => Some(f)
        case _ => None
      }
    }
    def combineWith(other: Cont)(implicit symbols: Symbols): Cont = {
      if(this eq other) this else {
        val newConstraint = And(constraints, other.constraints)
        val (k, nc) = ((known, newConstraint: Exp) /: other.known.toSeq) {
          case ((known, nc), (v, s2)) =>
            object EquivalentsVariables {
              def unapply(e: Var): Some[Set[Var]] = {
                known.get(e) match {
                  case Some(StrongValue(Var(e_next))) => Some(Set(e, e_next) ++ unapply(e_next).get)
                  case _ => Some(Set())
                }
              }
            }

            object BestEval {
              def unapply(e: Exp): Some[Exp] = e match {
                case Var(e_next) => Some(known.get(e_next).flatMap{
                  case StrongValue(e2) => unapply(e2)
                  case _ => None
                }.getOrElse(e))
                case e => Some(e)
              }
            }

            object WeakLink {
              def unapply(e: Var): Option[Var] = {
                if(known.get(e).forall(_.isInstanceOf[OriginalValue])) {
                  Some(e)
                } else {
                  known.get(e).flatMap{
                    case StrongValue(Var(e_next)) => unapply(e_next)
                    case _ => None
                  }
                }
              }
            }

            known.get(v) match {
              case None => (known + (v -> s2), nc)
              case Some(s) =>
                s2 match {
                  case AllValues =>
                    s match {
                      case AllValues => (known, nc)
                      case _ => throw new Exception(s"Tried to updated an universally quantified variable with non-universally quantified variable : $this.combineWith($other)")
                    }
                  case InsertVariable(e) =>
                    s match {
                      case InsertVariable(e) if e == e => (known, nc)
                      case InsertVariable(e) if !isValue(e) && isValue(e) => (known, nc)
                      case InsertVariable(e) if isValue(e) && !isValue(e) => (known + (v -> s2), nc)
                      case _ => throw new Error(s"Attempt at inserting a variable $v already known: $this.combineWith($other)")
                    }
                  case OriginalValue(e) => (known, nc) // No update needed.
                  case StrongValue(Var(EquivalentsVariables(knownSameVarsAse2))) if knownSameVarsAse2(v) => (known, nc)
                  case StrongValue(e2@BestEval(e2_eval)) =>
                    @inline def default(e: Exp) = (known, nc &<>& (e === e2))

                    s match {
                      case OriginalValue(e) => (known + (v -> s2), nc) // We replace the original value with the strong one
                      case StrongValue(e) if e == e2 => (known, nc)
                      case StrongValue(BestEval(e_eval)) if e_eval == e2_eval => (known, nc)
                      case StrongValue(Var(EquivalentsVariables(knownSameVarsAsV))) if isVar(e2) && knownSameVarsAsV(e2.asInstanceOf[Var]) =>
                        (known, nc) // Don't need to add this.
                      case StrongValue(Var(e)) if !(known contains e) => (known + (e -> StrongValue(v)), nc)
                      case StrongValue(Var(e@WeakLink(e_with_original))) =>
                        (known + (e_with_original -> StrongValue(e2)), nc)
                      case StrongValue(e) if isVar(e2) && known.get(e2.asInstanceOf[Var]).forall(_.isInstanceOf[OriginalValue]) =>
                        (known + (e2.asInstanceOf[Var] -> StrongValue(v)), nc)
                      case StrongValue(e) =>
                        commands.view.map{ command => command.merge(e2, e)}.find(_.nonEmpty).flatten match {
                          case Some((newExp, newAssign)) =>
                            val (newKnown, newConstraint) = ((known, nc) /: newAssign) {
                              case ((known, nc), xsy@(x, sy)) if !(this.known contains x) || this.known(x).isInstanceOf[OriginalValue] =>
                                (known + xsy, nc)
                              case ((known, nc), (x, sy@StrongValue(Var(y)))) if !(this.known contains y) || this.known(y).isInstanceOf[OriginalValue] =>
                                (known + (y -> StrongValue(x)), nc)
                              case ((known, nc), (x, sy)) =>
                                (known, nc &<>& sy.getConstraint(x))
                            }

                            (newKnown + (v -> StrongValue(newExp)), newConstraint)
                          case None =>
                            (e, e2) match {
                              case (Var(WeakLink(e_weak)), BestEval(e2_eval)) =>
                                (known + (e_weak -> StrongValue(e2_eval)), nc)
                              case (BestEval(e_eval), Var(WeakLink(e2_weak))) =>
                                (known + (e2_weak -> StrongValue(e_eval)), nc)
                              case (Var(WeakLink(e_weak)), Var(WeakLink(e2_weak))) if known(e_weak) == known(e2_weak) =>
                                (known, nc)
                              case _ =>
                                default(e)
                            }
                        }
                      case _ => throw new Error(s"Impossible to merge these values: $this.combineWith($other)")
                    }
                }
            }
        }
        Cont(k, nc)
      }
    } /: perfect.Log.prefix(s"combineWith($this,$other) = ")

    def combineWith(assignment: (Var, KnownValue))(implicit symbols: Symbols): Cont = {
      this combineWith Cont(Map(assignment))
    }

    // We remove all the given argument names from the formula because they are not going to be used anymore.
    def removeArgs(argNames: Seq[Var]): Cont = {
      val newKnown = (known /: argNames) {
        case (known, v) =>
          if(!(known contains v) ||
            known.exists{ case (k, value) => value.exists(exists{ case `v` => true case _ => false})} ||
            exists{ case `v` => true case _ => false}(this.constraints)) { // we keep it.
            known
          } else { // We remove it, it is useless if it does not appear in the constraints.
            known - v
          }
      }
      Cont(newKnown, constraints)
    }

    private lazy val knownToString: String = known.toSeq.map{
      case (k, StrongValue(e)) => k.toString + "=>" + e
      case (k, OriginalValue(e)) => k.toString + "->" + e
      case (k, AllValues) => "\u2200" + k
      case (k, InsertVariable(e)) => k.toString + ":=" + e
    }.mkString(", ")
    override def toString = {
      def suffixIfNotEmpty(e: String) = if(e != "") (if(constraints == ExpTrue) e else e + ", " + constraints.toString()) else constraints.toString()
      "[" + suffixIfNotEmpty(knownToString) + "]"
    }

    /** Returns an expression equal to the value of vd*/
    def getOrElse(v: Var, e: =>Exp): Exp = {
      findConstraintValue(v).getOrElse(e)
    }

    /** Finds the 'value' of a variable in the lhs of a constraint*/
    def findConstraintValue(v: Var): Option[Exp] = {
      known.get(v).flatMap(_.getValue).flatMap{
        case Var(v) => findConstraintValue(v).orElse(Some(v))
        case x => Some(x)
      }
    }

    /** Find the value of a variable only if it is strongly connected */
    def findStrongConstraintValue(v: Var): Option[Exp] = {
      known.get(v).flatMap{ case StrongValue(e) => Some(e) case _ => None }.flatMap{
        case Var(v) => findStrongConstraintValue(v).orElse(Some(v))
        case x => Some(x)
      }
    }

    /** Finds the value of an element in a map, in the formula */
/*    def findConstraintVariableOrLiteral(m: MapApply): Exp = m match {
      case MapApply(v: Var, key) =>
        findConstraintValue(v) match {
          case Some(FiniteMap(pairs, _, _, _)) =>
            pairs.find(_._1 == key).map(_._2).getOrElse{
              throw new Exception(s"Could not find key/value $v -> $key in "+this)
            }
          case _ =>
            throw new Exception(s"Could not find key/value $v -> $key in "+this)
        }
      case MapApply(v: MapApply, k) =>
        findConstraintVariableOrLiteral(MapApply(findConstraintVariableOrLiteral(v), k))
      case _ => throw new Exception(s"Not a well formed MapApply: $m")
    }*/
  }


  /** Previously 'ProgramFormula'*/
  object ContExp {
    def repairArguments(inFormula: Cont,
                        arguments: Seq[(Exp, ContExp)])(implicit symbols: Symbols, cache: Cache): Stream[(Seq[Exp], Cont)] = {
      val argumentsReversed = arguments.map { case (arg, expected) =>
        repair(ContExp(arg, inFormula), expected)
      }
      regroupArguments(argumentsReversed)
    }

    // Given a ProgramFormula for each of the fields, returns a list of expr and a single formulas
    def regroupArguments(arguments: Seq[Stream[ContExp]])
                        (implicit symbols: Symbols, cache: Cache): Stream[(List[Exp], Cont)] = {
      inox.utils.StreamUtils.cartesianProduct(arguments).map(combineResults)
    }

    // Given a ProgramFormula for each of the fields, returns a list of expr and a single formulas
    def combineResults(seq: List[ContExp])
                      (implicit symbols: Symbols, cache: Cache): (List[Exp], Cont) = {
      val (lb, f) = ((ListBuffer[Exp](), Cont()) /: seq) {
        case total@((ls, f1), (ContExp(l, f2))) =>
          (ls += l, f1 combineWith f2)
      }
      (lb.toList, f)
    }
  }

  /** Previously 'ProgramFormula'*/
  case class ContExp(exp: Exp, context: Cont = Cont()) {
    lazy val freeVars: Set[Var] = freeVariables(exp)
    lazy val unchanged: Set[Var] = freeVars -- context.varsToAssign

    override def toString = exp.toString + s" [$context]" + (if(canDoWrapping) " (wrapping enabled)" else "") + (if(isWrappingLowPriority) " (avoid wrap)" else "")
    var canDoWrapping = false

    def wrappingEnabled: this.type = {
      this.canDoWrapping = true
      this
    }

    def withComputedValue(e: Exp): this.type = {
      givenValue = Some(e)
      this
    }
    def withComputedValue(e: Option[Exp]): this.type = {
      givenValue = givenValue.orElse(e)
      this
    }

    lazy val simplifiedExpr: Exp = {
      if(isVar(exp)) {
        context.findConstraintValue(exp.asInstanceOf[Var]).getOrElse(exp)
      } else exp
    }

    // Can be set-up externally to bypass the computation of the function value.
    // Must be set before a call to functionValue using .withComputedValue
    private var givenValue: Option[Exp] = None

    lazy val bodyDefinition: Option[Exp] = context.assignments.map(f => f(exp))

    def getFunctionValue(implicit cache: Cache, symbols: Symbols): Option[Exp] = {
      givenValue match {
        case Some(e) => givenValue
        case None =>
          if(isValue(exp)) {
            givenValue = Some(exp)
            givenValue
          } else {
            context.assignments match {
              case Some(f) =>
                val res = maybeEvalWithCache(f(exp))
                givenValue = res
                res
              case None =>
                exp match {
//                  case FunctionInvocation(_, _, _) => None
                  case _ =>
                    // Maybe we can generate the value out of the constraints still.
                    var tmp = exp
                    var prev = Set[Exp]()
                    while(freeVariables(tmp).nonEmpty && !(prev contains tmp)) {
                      prev = prev + tmp
                      val mapping = freeVariables(tmp).map { v =>
                        v -> context.findConstraintValue(v).getOrElse(v)
                      }.toMap
                      tmp = replace(mapping, tmp)
                    }
                    if(freeVariables(tmp).isEmpty) {
                      Some(tmp)
                    } else None
                }
            }
          }
      }
    }

    def functionValue(implicit cache: Cache, symbols: Symbols): Exp = {
      givenValue match {
        case Some(e) => e
        case None =>
          val res = {
            if((freeVars -- context.known.keySet).nonEmpty) {
              throw new Exception(s"[Internal error] Tried to compute a function value but not all variables were known (only ${context.known.keySet} are).\n$this")
            }
            context.assignments.flatMap(wrapper => maybeEvalWithCache(wrapper(exp))).get
          }
          givenValue = Some(res)
          res
      }
    }

    /** Uses the result of a ContExp by wrapping the expression */
    def wrap(f: Exp => Exp): ContExp = {
      val newProgram = f(exp)
      ContExp(newProgram, context)
    }

    var isWrappingLowPriority: Boolean = false

    def wrappingLowPriority(b: Boolean = true): this.type = {
      isWrappingLowPriority = true
      this
    }

    /** Replaces the expression with another, for defining sub-problems mostly. */
    def subExpr(f: Exp): ContExp = {
      ContExp(f, context).wrappingLowPriority(isWrappingLowPriority)
    }

    /*def withoutConstraints(): ContExp = {
      ContExp(expr)
    }*/

    /** Returns the original assignments marked as original
      * Require known to be set. */
    def assignmentsAsOriginals(): ContExp = {
      this.copy(context = this.context.assignmentsAsOriginals)
    }

    /** Augment this expr with the given formula */
    def combineWith(f: Cont)(implicit symbols: Symbols): ContExp = {
      ContExp(exp, context combineWith f).wrappingLowPriority(isWrappingLowPriority)
    }

    /** Removes all insertVar from the formula and inserts them into the program.*/
    def insertVariables(): ContExp = {
      val inserted: Map[Var, KnownValue] = context.known.collect[(Var, KnownValue), Map[Var, KnownValue]]{
        case (v, InsertVariable(e)) => (v, StrongValue(e))
      }
      val remaining = context.known.filter{
        case (v, InsertVariable(e)) => false
        case _ => true
      }
      val newCont = if(inserted.isEmpty) context else context.copy(known = remaining)
      val assignment = Cont(inserted).assignments

      if(inserted.nonEmpty && assignment.nonEmpty) {
        ContExp(assignment.get(exp), newCont)
      } else this
    }
  }
}
