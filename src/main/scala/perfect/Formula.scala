package perfect

import inox.FreshIdentifier
import inox.trees._
import inox.trees.dsl._
import perfect.ProgramFormula._
import perfect.ReverseProgram.Cache

import scala.collection.mutable.ListBuffer

/**
  * Created by Mikael on 06/04/2017.
  */

object Formula {
  /** A deterministic constructor for Formula */
  def apply(ve: (Variable, KnownValue)): Formula = Formula(Map(ve))

  def apply(formulas: Iterable[Formula])(implicit symbols: Symbols): Formula = {
    (Formula() /: formulas)(_ combineWith _)
  }

  /** Automatic simplification of EXPR1 && EXPR2 if one is true.*/
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

  protected def inlineSimpleFormulas(e: Formula): Formula = {
    import StringConcatExtended._
    import semanticlenses._
    implicit val symbols = Utils.defaultSymbols
    def evalExprIfNeeded(e: Expr) =
      ProgramFormula.customProgramFormulas.view.map{
        cpf => cpf.Eval.unapply(e)
      }.find(_.nonEmpty).flatten.getOrElse(e)
    val result = e.known.map{
      case (v, so@StrongOrOriginal(e, builder)) =>
        val newE = evalExprIfNeeded(e)
        if(newE ne e) {
          v->builder(newE)
        } else v->so
      case m => m
    }
    val TopLevelAnds(exprs) = e.constraints
    val newExprs = exprs.map{
      case equ@Equals(v, e) =>
        val newE = evalExprIfNeeded(e)
        val newV = evalExprIfNeeded(v)
        if((newE ne e) || (newV ne v))
          Equals(newV, newE)
        else equ
      case m => m
    }
    Formula(result, and(newExprs: _*))
  }
}

sealed trait KnownValue {
  def getValue: Option[Expr]
  def getConstraint(k: Variable): Expr
  def map(f: Expr => Expr): KnownValue
  def exists(f: Expr => Boolean): Boolean = getValue.exists(x => f(x))
}
case class StrongValue(e: Expr) extends KnownValue {
  def getValue = Some(e)
  def getConstraint(k: Variable) = k === e
  def map(f: Expr => Expr): StrongValue = {
    StrongValue(f(e))
  }
}
case class OriginalValue(e: Expr) extends KnownValue {
  def getValue = Some(e)
  def getConstraint(k: Variable) = E(Utils.original)(k === e)
  def map(f: Expr => Expr): OriginalValue = {
    OriginalValue(f(e))
  }
}
case class InsertVariable(e: Expr) extends KnownValue {
  def getValue = Some(e)
  def getConstraint(k: Variable) = k === e //throw new Exception("[Internal error] tried to get a constraint on an inserted variable")
  def map(f: Expr => Expr): InsertVariable = {
    InsertVariable(f(e))
  }
}
case object AllValues extends KnownValue {
  def getValue = None
  def getConstraint(k: Variable) = BooleanLiteral(true)
  def map(f: Expr => Expr): AllValues.type = this
} // Universally quantified variables.

object StrongOrOriginal {
  def unapply(e: KnownValue): Option[(Expr, Expr => KnownValue)] = e match {
    case StrongValue(e) => Some((e, (StrongValue(_))))
    case OriginalValue(e) => Some((e, (OriginalValue(_))))
    case AllValues => None
    case InsertVariable(_) => None
  }
}

case class Formula(known: Map[Variable, KnownValue] = Map(), constraints: Expr = BooleanLiteral(true)) {
  import Formula._
  // Can contain middle free variables.
  lazy val varsToAssign: Set[Variable] = known.keySet ++ exprOps.variablesOf(constraints)

  lazy val assignmentsAsOriginals: Formula = {
    Formula(known.map{ case (k, StrongValue(e)) => (k, OriginalValue(e)) case kv => kv})
  }

  // A list of partial assignments if there is no further constraints.
  lazy val partialAssignments: Option[(Expr => Expr, List[(Variable, KnownValue)])] = {
    def rec(constraints: Seq[(Variable, KnownValue)], seen: Set[Variable]): (Expr => Expr, List[(Variable, KnownValue)]) = {
      if(constraints == Nil) return ((x: Expr) => x, Nil)
      // Possibility to build all assignments in one shot.
      val (sNewF, newSeen, remaining) = ((None: Option[Expr => Expr], seen, ListBuffer[(Variable, KnownValue)]()) /: constraints) {
        case ((optF, seen, remaining), equ@(v, StrongOrOriginal(e, _))) if (exprOps.variablesOf(e) -- seen).isEmpty =>
          optF match {
            case None => (Some((x: Expr) => Let(v.toVal, e, x)), seen + v, remaining)
            case Some(f) => (Some((x: Expr) => f(Let(v.toVal, e, x))), seen + v, remaining)
          }
        case ((optF, seen, remaining), equ) =>
          (optF, seen, remaining += equ)
      }
      val newF = sNewF.getOrElse((x: Expr) => x)
      if(remaining.length == 0 || newSeen.size == seen.size) { // no progress
        (newF, remaining.toList)
      } else {
        val (rf, remaining2) = rec(remaining, newSeen)
        ((x: Expr) => newF(rf(x)), remaining2)
      }
    }
    if(constraints != BooleanLiteral(true)) None else {
      Some(rec(known.toSeq, Set()))
    }
  }

  /** If the constraints are complete, i.e. all variables can be defined, then we can generate a let-wrapper. */
  lazy val assignments: Option[Expr => Expr] = { // We know that variables appear only once in the lhs of the seq
    partialAssignments.flatMap{
      case (f, Nil) => Some(f)
      case _ => None
    }
  }

  /** Checks if there are unwanted circularities. Useful to debug. */
  lazy val isCircular = known.exists {
    case (k, StrongValue(v: Variable)) =>
      inox.utils.fixpoint(
        (s: Set[Variable]) => s ++ s.flatMap{
          (k2: Variable) => known.get(k2).collect{
            case StrongValue(v: Variable) => v
          }
        }
      )(Set(v))(k)
    case _ => false
  }

  import semanticlenses._

  def combineWith(other: Formula)(implicit symbols: Symbols): Formula = {
    if(this eq other) this else
    if(this.known.isEmpty && this.constraints == BooleanLiteral(true)) other else {
      val TopLevelAnds(ands) = constraints &<>& other.constraints
      val newConstraint = and(ands.distinct: _*)
      val (k, nc) = ((known, newConstraint: Expr) /: other.known.toSeq) {
        case ((known, nc), vs2@(v, s2)) =>
          assert(!Formula(known).isCircular, s"Circularity: ${Formula.this} and other = ${other}, Combining \n${known.map{case (k, v) => k.toString + "->" + v}.mkString("\n")}\n and\n$v -> $s2")

          object EquivalentsVariables {
            def unapply(e: Variable): Some[Set[Variable]] = {
              known.get(e) match {
                case Some(StrongValue(e_next: Variable)) => Some(Set(e, e_next) ++ unapply(e_next).get)
                case _ => Some(Set())
              }
            }
          }

          object BestEval {
            def unapply(e: Expr): Some[Expr] = e match {
              case e_next: Variable => Some(known.get(e_next).flatMap{
                case StrongValue(e2) => unapply(e2)
                case _ => None
              }.getOrElse(e))
              case e => Some(e)
            }
          }

          object WeakLink {
            def unapply(e: Variable): Option[Variable] = {
              if(known.get(e).forall(_.isInstanceOf[OriginalValue])) {
                Some(e)
              } else {
                known.get(e).flatMap{
                  case StrongValue(e_next: Variable) => unapply(e_next)
                  case _ => None
                }
              }
            }
          }
          import Utils.isValue

          known.get(v) match {
            case None => (known + (v -> s2), nc)
            case Some(s) =>
              s2 match {
                case AllValues =>
                  s match {
                    case AllValues => (known, nc)
                    case _ => throw new Exception(s"Tried to updated an universally quantified variable with non-universally quantified variable : $this.combineWith($other)")
                  }
                case InsertVariable(e2) =>
                  s match {
                    case InsertVariable(e) if e == e2 => (known, nc)
                    case InsertVariable(e) if isValue(e2) && !isValue(e) => (known, nc)
                    case InsertVariable(e) if isValue(e) && !isValue(e2) => (known + (v -> s2), nc)
                    case _ => throw new Error(s"Attempt at inserting a variable $v already known: $this.combineWith($other)")
                  }
                case OriginalValue(e2) => (known, nc) // No update needed.

                case StrongValue(EquivalentsVariables(knownSameVarsAse2)) if knownSameVarsAse2(v) => (known, nc)

                case StrongValue(e2@BestEval(e2_eval)) =>
                  @inline def default(e: Expr) = {
                    println(s"Warning: in this = ${this} and other = ${other}, Combining \n${known.map { case (k, v) => k.toString + "->" + v }.mkString("\n")}\n and\n$v -> StrongValue($e2) not supported")
                    (known, nc &<>& (e === e2))
                  }

                  s match {
                    case OriginalValue(e) => (known + (v -> s2), nc) // We replace the original value with the strong one
                    case StrongValue(e) if e == e2 => (known, nc)
                    case StrongValue(BestEval(e_eval)) if e_eval == e2_eval => (known, nc)
                    case StrongValue(EquivalentsVariables(knownSameVarsAsV)) if e2.isInstanceOf[Variable] && knownSameVarsAsV(e2.asInstanceOf[Variable]) =>
                      (known, nc) // Don't need to add this.

                    case StrongValue(e: Variable) if !(known contains e) => (known + (e -> StrongValue(v)), nc)
                    case StrongValue(e@WeakLink(e_with_original)) =>
                      (known + (e_with_original -> StrongValue(e2)), nc)
                    case StrongValue(e) if e2.isInstanceOf[Variable] && known.get(e2.asInstanceOf[Variable]).forall(_.isInstanceOf[OriginalValue]) =>
                      (known + (e2.asInstanceOf[Variable] -> StrongValue(v)), nc)

                    case StrongValue(e) =>


                      ProgramFormula.mergeProgramFormula.view.map { command => command.merge(e2, e) }.find(_.nonEmpty).flatten match {
                        case Some((newExp, newAssign)) =>
                          val (newKnown, newConstraint) = ((known, nc) /: newAssign) {
                            case ((known, nc), xsy@(x, sy)) if !(this.known contains x) || this.known(x).isInstanceOf[OriginalValue] =>
                              (known + xsy, nc)
                            case ((known, nc), xsy@(x, sy@StrongValue(y: Variable))) if !(this.known contains y) || this.known(y).isInstanceOf[OriginalValue] =>
                              (known + (y -> StrongValue(x)), nc)
                            case ((known, nc), xsy@(x, sy)) =>
                              (known, nc &<>& sy.getConstraint(x))
                          }

                          (newKnown + (v -> StrongValue(newExp)), newConstraint)
                        case None =>
                          (e, e2) match {
                            case (WeakLink(e_weak), BestEval(e2_eval)) =>
                              (known + (e_weak -> StrongValue(e2_eval)), nc)
                            case (BestEval(e_eval), WeakLink(e2_weak)) =>
                              (known + (e2_weak -> StrongValue(e_eval)), nc)
                            case (WeakLink(e_weak), WeakLink(e2_weak)) if known(e_weak) == known(e2_weak) =>
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
      Formula(k, nc)
    }
  } // /: Log.prefix(s"combineWith($this,$other) = ")// ensuring { (f: Formula) => !f.isCircular }

  def combineWith(assignment: (Variable, KnownValue))(implicit symbols: Symbols): Formula = {
    this combineWith Formula(Map(assignment))
  }

  // We remove all the given argument names from the formula because they are not going to be used anymore.
  def removeArgs(argNames: Seq[Variable]): Formula = {
    val newKnown = (known /: argNames) {
      case (known, v) =>
      if(!(known contains v) ||
        known.exists{ case (k, value) => value.exists(va => exprOps.count{ case `v` => 1 case _ => 0}(va) >= 1)} ||
        exprOps.exists{ case `v` => true case _ => false}(this.constraints)) { // we keep it.
        known
      } else { // We remove it, it is useless if it does not appear in the constraints.
        known - v
      }
    }
    Formula(newKnown, constraints)
  }

  private lazy val knownToString: String = known.toSeq.sortBy(_._1.toString).map{
    case (k, StrongValue(e)) => k.toString + "=>" + e
    case (k, OriginalValue(e)) => k.toString + "->" + e
    case (k, AllValues) => "\u2200" + k
    case (k, InsertVariable(e)) => k.toString + ":=" + e
  }.mkString(", ")
  override def toString = {
    def suffixIfNotEmpty(e: String) = if(e != "") (if(constraints == BooleanLiteral(true)) e else e + ", " + constraints.toString()) else constraints.toString()
    "[" + suffixIfNotEmpty(knownToString) + "]"
  }
  private lazy val unknownConstraintsVars: Set[ValDef] = (exprOps.variablesOf(constraints) ++ known.keySet).map(_.toVal)

  /** Returns an expression equal to the value of vd*/
  def getOrElse(v: Variable, e: =>Expr): Expr = {
    findConstraintValue(v).getOrElse(e)
  }

  /** Finds the 'value' of a variable in the lhs of a constraint*/
  def findConstraintValue(v: Variable): Option[Expr] = {
    if(Thread.currentThread().getStackTrace.length > 1000) {
      println(s"Trying to get variable $v from $this is looping")
      throw new Exception("loop")
    }
    known.get(v).flatMap(_.getValue).flatMap{
      case v: Variable => findConstraintValue(v).orElse(Some(v))
      case x => Some(x)
    }
  }

  /** Find the value of a variable only if it is strongly connected */
  def findStrongConstraintValue(v: Variable): Option[Expr] = {
    known.get(v).flatMap{ case StrongValue(e) => Some(e) case _ => None }.flatMap{
      case v: Variable => findStrongConstraintValue(v).orElse(Some(v))
      case x => Some(x)
    }
  }

  /** Finds the value of an element in a map, in the formula */
  def findConstraintVariableOrLiteral(m: MapApply): Expr = m match {
    case MapApply(v: Variable, key) =>
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
  }

  // The assignments and the formula containing the other expressions.
  def determinizeAll(freeVariables: Seq[Variable] = varsToAssign.toSeq)(implicit symbols: Symbols): Stream[Map[Variable, Expr]] = {
    Log(s"Trying to get all solutions for $varsToAssign of \n" + this)
    val simplified = inlineSimpleFormulas(this)
    Log(s"Simplified: $simplified")
    val streamOfSolutions = simplified.partialAssignments match {
      case Some((wrapper, remaining)) if remaining.forall(x => x._2 == AllValues) =>
        ReverseProgram.maybeEvalWithCache(wrapper(tupleWrap(freeVariables)))(symbols, new ReverseProgram.Cache()).toStream
      case e =>
        if(e.nonEmpty) Log(s"Warning: some equations could not be simplified: $e")
        val input = Variable(FreshIdentifier("input"), tupleTypeWrap(freeVariables.map(_.getType)), Set())
        val constraint = InoxConstraint(input === tupleWrap(freeVariables) &<>& simplified.constraints &<>&
          and(simplified.known.toSeq.map{ case (k, v) => v.getConstraint(k)}: _*))
        Log(s"Solving as $constraint")
        constraint.toStreamOfInoxExpr(input)
    }
    streamOfSolutions.map {
      case Tuple(args) => freeVariables.zip(args).map{ case (fv: Variable, expr: Expr) => fv -> expr }.toMap
      case e if freeVariables.length == 1 => Map(freeVariables.head -> e)
      case UnitLiteral() if freeVariables.length == 0 => Map[Variable, Expr]()
      case e =>
        throw new Exception(s"Other unexpected solution: $e")
    }
  }
}