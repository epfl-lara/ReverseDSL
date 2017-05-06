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
  import semanticlenses._
  def combineWith(other: Formula)(implicit symbols: Symbols): Formula = {
    if(this eq other) this else {
      val TopLevelAnds(ands) = constraints &<>& other.constraints
      val newConstraint = and(ands.distinct: _*)
      val (k, nc) = ((known, newConstraint: Expr) /: other.known.toSeq) {
        case ((known, nc), (v, s@AllValues)) =>
          known.get(v) match {
            case None => (known + (v -> s), nc)
            case Some(s2@AllValues) => (known, nc)
            case _ => throw new Exception(s"Tried to updated an universally quantified variable with non-universally quantified variable : $this.combineWith($other)")
          }
        case ((known, nc), (v, s@InsertVariable(e))) =>
          known.get(v) match {
            case None => (known + (v -> s), nc)
            case Some(s2@InsertVariable(e2)) if e2 == e => (known, nc)
            case Some(s2@InsertVariable(_: StringConcat | _: Variable)) if e.isInstanceOf[StringLiteral] =>
              (known, nc)
            case Some(s2@InsertVariable(StringLiteral(_))) if e.isInstanceOf[StringConcat] || e.isInstanceOf[Variable] =>
              (known + (v -> s), nc)
            case Some(_) => throw new Error(s"Attempt at inserting a variable $v already known: $this.combineWith($other)")
          }
        case ((known, nc), (v, s@StrongValue(e))) =>
          @inline def default(e2: Expr) = (known, nc &<>& (e === e2))

          known.get(v) match {
            case None => (known + (v -> s), nc)
            case Some(OriginalValue(e)) => (known + (v -> s), nc) // We replace the original value with the strong one
            case Some(StrongValue(e2)) if e2 == e => (known, nc)
            case Some(StrongValue(e2: Variable)) if !(known contains e2) => (known + (e2 -> StrongValue(v)), nc)
            case Some(StrongValue(e2)) if (exprOps.variablesOf(e2).isEmpty && e.isInstanceOf[Variable] && // Particular merging case quite useful.
              !(this.known contains e.asInstanceOf[Variable]) &&
              other.known.get(e.asInstanceOf[Variable]).exists(_.isInstanceOf[OriginalValue])) /* /:
            Log.prefix(s"shortcut ($e2 is value: ${Utils.isValue(e2)}) (e = $e is variable: ${e.isInstanceOf[Variable]}) " +
              s"(this.known contains e: ${e.isInstanceOf[Variable] && !(known contains e.asInstanceOf[Variable])})" +
              s"(${other.known} contains e as original: ${e.isInstanceOf[Variable] &&  other.known.get(e.asInstanceOf[Variable]).exists(_.isInstanceOf[OriginalValue])}):")*/
            =>
              (known + (e.asInstanceOf[Variable] -> StrongValue(e2)) + (v -> s), nc)
            case Some(StrongValue(e2@PatternMatch.Expr(before, variables, forClone))) =>
              e match {
                case CloneTextMultiple.Expr(left2, textVarRight2) =>
                  e2 match {
                    case CloneTextMultiple.Expr(left1, textVarRight1) =>
                      CloneTextMultiple.Expr.merge(left1, textVarRight1, left2, textVarRight2) match {
                        case Some((cm, news)) => (known + (v -> StrongValue(cm)) ++ news, nc)
                        case None => default(e2)
                      }
                    case _ => ???
                  }

                case PatternMatch.Expr(before2, variables2, forClone2) =>
                  PatternMatch.Expr.merge(before, variables, forClone, before2, variables2, forClone2) match {
                    case Some((cm, news)) => (known + (v -> StrongValue(cm)) ++ news, nc)
                    case None => default(e2)
                  }
                case _ => default(e2)
              }
            case Some(StrongValue(e2@ADT(tpe, vars))) if vars.forall(_.isInstanceOf[Variable]) =>
              e match {
                case ADT(tpe2, vars2) if vars2.forall(_.isInstanceOf[Variable]) && tpe == tpe2 =>
                  val vvars1: Seq[Variable] = vars.collect { case v: Variable => v }
                  val vvars2: Seq[Variable] = vars2.collect { case v: Variable => v }
                  ((known, nc) /: vvars1.zip(vvars2)) {
                    case ((known, nc), (x1: Variable, x2: Variable)) =>
                      (this.known.get(x1), other.known.get(x2)) match {
                        case (Some(OriginalValue(o)), Some(StrongOrOriginal(_))) =>
                          (known + (x1 -> StrongValue(x2)), nc)
                        case (Some(StrongValue(sv)), Some(OriginalValue(_))) =>
                          (known + (x2 -> StrongValue(x1)), nc)
                        case (None, Some(StrongOrOriginal(_))) =>
                          (known + (x1 -> StrongValue(x2)), nc)
                        case (Some(StrongOrOriginal(_)), None) =>
                          (known + (x2 -> StrongValue(x1)), nc)
                        case (Some(StrongValue(sv1)), Some(StrongValue(sv2))) =>
                          (known, nc &<>& sv1 === sv2)
                        case e => throw new Exception("Did not implement something for this case: $e")
                      }
                  }
                case _ => (known, nc &<>& (v === e2))
              }
            case Some(StrongValue(e2)) => default(e2)
            case Some(AllValues) => throw new Error(s"Attempt at assigning an universally quantified variable: $this.combineWith($other)")
          }
        case ((known, nc), (v, s@OriginalValue(e))) =>
          known.get(v) match {
            case None => (known + (v -> s), nc)
            case _ => (known, nc) // No update needed.
          }
      }
      Formula(k, nc)
    }
  } /: Log.prefix(s"combineWith($this,$other) = ")

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

  private lazy val knownToString: String = known.toSeq.map{
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
        ReverseProgram.maybeEvalWithCache(wrapper(tupleWrap(freeVariables)))(new ReverseProgram.Cache(), symbols).toStream
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