package perfect

import inox.FreshIdentifier
import inox.trees._
import inox.trees.dsl._
import perfect.ProgramFormula._
import perfect.ReverseProgram.{Cache, evalWithCache, letm}

/**
  * Created by Mikael on 06/04/2017.
  */

object Formula {
  /** A deterministic constructor for Formula */
  def apply(known: Map[ValDef, Expr]): Formula = {
    val f = Formula(and(known.toSeq.map(x => x._1.toVariable === x._2): _*))
    f.givenKnown = Some(known)
    f
  }
  def apply(formulas: Iterable[Formula]): Formula = {
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
    val TopLevelAnds(exprs) = e.unknownConstraints
    implicit val symbols = Utils.defaultSymbols
    val newExprs = exprs.map {
      case Equals(v: Variable, StringInsert.Expr(left, middle, right, direction)) =>
        Equals(v, StringLiteral(left + middle + right))
      case Equals(v: Variable, ListInsert.Expr(tpe, left, middle, right)) =>
        Equals(v, ListLiteral(left ++ middle ++ right, tpe))
      case e@Equals(v: Variable, TreeModification.Expr(tpeGlobal, tpeLocal, original, modified, argsList)) =>
        TreeModification.LambdaPath(original, argsList, modified).map(l => Equals(v, l)).getOrElse(e)
      case e => e
    }
    if(newExprs != exprs) {
      Formula(and(newExprs: _*))
    } else e
  }

  /** We remove maybes on values which are already known.
    * Second we unwrap the maybe if the variable appears only in this maybe, modulo removing its occurs in a map used only once. */
  protected def removeUselessMaybes(e: Formula): Formula = {
    val TopLevelAnds(exprs) = e.unknownConstraints
    val known = exprs.flatMap{
      case Equals(v: Variable, e) =>
        List(v -> e)
      case _ => Nil
    }.toMap
    val varCount = exprOps.variablesOf(e.unknownConstraints).map{ v =>
      v -> exprOps.count{
        case v2: Variable if v2 == v => 1
        case Equals(v2: Variable, fm: FiniteMap) =>
          // We do not count occurrences of the values of a (map used only once) because they are only definitions.
          if(exprOps.count{ case v3: Variable if v3 == v2 => 1 case _ => 0}(e.unknownConstraints) == 1) {
            -exprOps.count{ case v4: Variable if v4 == v => 1 case _ => 0}(fm)
          } else 0
        case Equals(v2: Variable, fm@ADT(tpe, args)) =>
          // We do not count occurrences of the values of an (ADT used only once) because they are only definitions.
          if(exprOps.count{ case v3: Variable if v3 == v2 => 1 case _ => 0}(e.unknownConstraints) == 1) {
            -exprOps.count{ case v4: Variable if v4 == v => 1 case _ => 0}(fm)
          } else 0
        case _ => 0
      }(e.unknownConstraints)
    }.toMap /: Log.varCount

    val exprs2 = exprs.flatMap {
      case FunctionInvocation(Utils.original, Seq(), Seq(Equals(v: Variable, e: Expr))) if Utils.isValue(e) && (known contains v) =>
        Nil
      case FunctionInvocation(Utils.original, Seq(), Seq(Equals(e: Expr, v: Variable))) if Utils.isValue(e) && (known contains v) =>
        Nil
      case FunctionInvocation(Utils.original, Seq(), Seq(eq@Equals(v: Variable, e: Expr))) if varCount(v) == 1 =>
        List(eq)
      case FunctionInvocation(Utils.original, Seq(), Seq(eq@Equals(e: Expr, v: Variable))) if varCount(v) == 1 =>
        List(eq)
      case e => List(e)
    }.distinct /: Log.exprs2
    if(exprs2 != exprs) removeUselessMaybes(Formula(and(exprs2: _*))) else e
  }

  protected def removeUselessVariables(e: Formula, freeVariables: Set[Variable]): Formula = {
    // Remove all variables of freeVariables in formula appearing only once in an equation.
    val TopLevelAnds(exprs) = e.unknownConstraints
    val varCount = exprOps.variablesOf(e.unknownConstraints).map{ v =>
      v -> exprOps.count{
        case v2: Variable if v2 == v => 1
        case _ => 0
      }(e.unknownConstraints)
    }.toMap /: Log.varCount

    val exprs2 = exprs.flatMap {
      case Equals(v: Variable, e: Expr) if varCount(v) == 1 && !freeVariables(v) =>
        Nil
      case Equals(e: Expr, v: Variable) if varCount(v) == 1 && !freeVariables(v) =>
        Nil
      case e => List(e)
    }.distinct /: Log.exprs2
    if(exprs2 != exprs) removeUselessVariables(Formula(and(exprs2: _*)), freeVariables) else e
  }

  /*
  *   If a == Node(b, c) && a == Node(d, e) && a == Node(f, g), expands the equations to:
  *   a == Node(b, c) && b == d && c == e && b == f && c == g
  **/
  protected def unifyADTDeclarations(e: Formula): Formula = {
    val TopLevelAnds(exprs) = e.unknownConstraints
    val (adts, nonadts) = exprs.partition {
      case Equals(a: Variable, b: ADT) => true
      case Equals(b: ADT, a: Variable) => true
      case _ => false
    }
    val adtDefinitions: Map[Variable, Seq[ADT]] = adts.collect{
      case Equals(a: Variable, b: ADT) => (a, b)
      case Equals(b: ADT, a: Variable) => (a, b)
    }.groupBy(_._1).mapValues(v => v.map(_._2))
    if(adtDefinitions.exists{ kv => kv._2.map(_.adt).toSet.size > 1 }) { // Unsatisfiable if a variable equals to different ADTs
      return Formula(BooleanLiteral(false))
    }
    val res = Formula(adtDefinitions.map{
      case (v, adts) =>
        if(adts.isEmpty) {
          Formula() // Should not happen
        } else {
          Formula(and((v === adts.head) +: adts.tail.map{ adt => and(adt.args.zip(adts.head.args).map(kv => kv._1 === kv._2) :_*) }: _*))
        }
    }) combineWith Formula(and(nonadts:_*))
    if(res != e) unifyADTDeclarations(res) else res
  }

  protected def simplify(e: Formula, freeVariables: Set[Variable]) = {
    unifyADTDeclarations(removeUselessVariables(removeUselessMaybes(inlineSimpleFormulas(e)), freeVariables))
  }
}

case class Formula(unknownConstraints: Expr = BooleanLiteral(true)) {
  import Formula._

  // Can contain middle free variables.
  lazy val varsToAssign = known.keySet ++ (exprOps.variablesOf(unknownConstraints).map(_.toVal))

  //val TopLevelAnds(ands) = unknownConstraints
  //assert(ands.forall(x => !x.isInstanceOf[Lambda]))

  private var givenKnown: Option[Map[ValDef, Expr]] = None

  /** Subset of variables which are known. Careful: Does not detect incoherencies in the formula. */
  lazy val known: Map[ValDef, Expr] = givenKnown.getOrElse{
    val TopLevelAnds(ands) = unknownConstraints
    ands.flatMap {
      case Equals(v: Variable, e: Expr) if(Utils.isValue(e)) => // TODO: Try to remove "isValue"
        List(v.toVal -> e)
      case _ => Nil
    }.toMap
  }

  /** If the constraints are complete, i.e. all variables can be defined, then we can generate a let-wrapper. */
  lazy val assignments: Option[Expr => Expr] = {
    def rec(constraints: List[Expr], seen: Set[Variable]): Option[Expr => Expr] = {
      if(constraints == Nil) Some(x => x) else {
        val res = constraints.collectFirst[(Expr => Expr, Variable, Expr)]{
          case equ@Equals(v: Variable, e: Expr) if (exprOps.variablesOf(e) -- seen).isEmpty =>
            ((x: Expr) => Let(v.toVal, e, x), v, equ)
          case equ@Equals(e: Expr, v: Variable) if (exprOps.variablesOf(e) -- seen).isEmpty =>
            ((x: Expr) => Let(v.toVal, e, x), v, equ)
        }.orElse(constraints.collectFirst[(Expr => Expr, Variable, Expr)]{
          case equ@FunctionInvocation(Utils.original, Seq(), Seq(Equals(v: Variable, e: Expr)))
            if (exprOps.variablesOf(e) -- seen).isEmpty =>
            ((x: Expr) => Let(v.toVal, e, x), v, equ)
        }).flatMap{ fve =>
          val recursively =rec(constraints.filter(x => x != fve._3), seen + fve._2)
          if(seen(fve._2)) {
            fve._3 match {
              case FunctionInvocation(Utils.original, Seq(), Seq(Equals(v: Variable, e: Expr))) =>
                recursively // That's ok.
              case equ@Equals(v: Variable, e: Expr) =>
                None
              case equ@Equals(e: Expr, v: Variable) if (exprOps.variablesOf(e) -- seen).isEmpty =>
                None
            }
          } else {
            recursively.map(
              (g: Expr => Expr) => ((x: Expr) => fve._1(g(x))))
          }
        }
        if(res.isEmpty) Log(s"Could not reduce $constraints knowing $seen")
        res
      }
    }
    val TopLevelAnds(ands) = unknownConstraints
    rec(ands.toList.filter(x => x != BooleanLiteral(true)), Set())
  }

  def combineWith(other: Formula): Formula = {
    val TopLevelAnds(ands) = unknownConstraints &<>& other.unknownConstraints
    Formula(and(ands.distinct :_*))
  }

  def combineWith(b: Expr): Formula = {
    this combineWith Formula(b)
  }

  override def toString = "[" + unknownConstraints.toString() + "]"
  private lazy val unknownConstraintsVars: Set[ValDef] = exprOps.variablesOf(unknownConstraints).map(_.toVal)

  /** Returns an expression equal to the value of vd*/
  def getOrElse(vd: ValDef, e: =>Expr): Expr = {
    known.getOrElse(vd, {
      if(varsToAssign(vd)) {
        vd.toVariable
      } else e // The expression is unchanged, we return the original expression
    })
  }

  /** Finds the 'value' of a variable in the lhs of a constraint*/
  def findConstraintValue(v: Variable): Option[Expr] = {
    unknownConstraints match {
      case TopLevelAnds(ands) =>
        val possibleExprs = ands.toList.collect[Expr, List[Expr]] {
          case Equals(mapVar, value: Expr)
            if mapVar == v => value
        }.distinct
        if(possibleExprs.isEmpty){
          ands.collectFirst[Expr] {
            case FunctionInvocation(Utils.original, _, Seq(
            Equals(mapVar, value))) if mapVar == v => value
          }
        } else if(possibleExprs.length == 1) {
          Some(possibleExprs.head)
        } else { // We try to reunite expressions, for example when they are clones.
          if(possibleExprs.map(ProgramFormula(_)).forall{ case ProgramFormula.CloneTextMultiple(_, _) => true case _ => false}) {
            val first = ProgramFormula(possibleExprs.head)
            val pf = ((Some(first): Option[ProgramFormula]) /: possibleExprs.tail.map(ProgramFormula(_))) {
              case (None, _) => None
              case (Some(ProgramFormula.CloneTextMultiple(left, list)), ProgramFormula.CloneTextMultiple(left2, list2)) =>
                ProgramFormula.CloneTextMultiple.merge(left, list, left2, list2)
            }
            pf.map(_.expr)
          } else None
        }
      case _ => None
    }
  }

  def withoutFirstConstraintOn(v: Variable) = {
    val f = unknownConstraints match {
      case TopLevelAnds(ands) =>
        ands.span{
          case Equals(mapVar: Variable, value) if mapVar == v => false
          case _ => true
        } match {
          case (before, head::after) => and(before ++ after : _*)
          case (before, Nil) => and(before: _*)
        }
    }
    Formula(f)
  }

  /** Finds the value of an element in a map, in the formula */
  def findConstraintVariableOrLiteral(m: MapApply): Expr = m match {
    case MapApply(v: Variable, key) =>
      findConstraintValue(v) match {
        case Some(FiniteMap(pairs, _, _, _)) =>
          pairs.find(_._1 == key).map(_._2).getOrElse{
            throw new Exception(s"Could not find key/value $v -> $key in "+unknownConstraints)
          }
        case _ =>
          throw new Exception(s"Could not find key/value $v -> $key in "+unknownConstraints)
      }
    case MapApply(v: MapApply, k) =>
      findConstraintVariableOrLiteral(MapApply(findConstraintVariableOrLiteral(v), k))
    case _ => throw new Exception(s"Not a well formed MapApply: $m")
  }

  // The assignments and the formula containing the other expressions.
  def determinizeAll(freeVariables: Seq[ValDef] = varsToAssign.toSeq)(implicit symbols: Symbols): Stream[Map[ValDef, Expr]] = {

    Log(s"Trying to get all solutions for $varsToAssign of \n" + this)
    //val freeVariables = varsToAssign.toSeq
    val constraints = simplify(this, freeVariables.map(_.toVariable).toSet).unknownConstraints
    constraints match {
      case BooleanLiteral(true) => Stream(freeVariables.map(fv => fv -> known(fv)).toMap)
      case BooleanLiteral(false) => Stream.empty
      case constraints =>
        // First try to solve constraints ourselves if they are only assignments.
        val streamOfSolutions =         Formula(constraints).assignments match {
          case Some(wrapper) =>
            Stream(ReverseProgram.evalWithCache(wrapper(tupleWrap(freeVariables.map(_.toVariable))))(new ReverseProgram.Cache(), symbols))
          case None =>
            val input = Variable(FreshIdentifier("input"), tupleTypeWrap(freeVariables.map(_.getType)), Set())
            //println(s"input is of type ${input.getType}")
            val constraint = InoxConstraint(input === tupleWrap(freeVariables.map(_.toVariable)) && constraints)
            Log(s"Solving for $constraint")
            constraint.toStreamOfInoxExpr(input)
        }
        streamOfSolutions.map {
          case Tuple(args) => freeVariables.zip(args).map{ case (fv: ValDef, expr: Expr) => fv -> expr }.toMap
          case e if freeVariables.length == 1 =>
            Map(freeVariables.head -> e)
          case e =>
            Log("other solution : " + e)
            Map[ValDef, Expr]()
        }
    }
  }
}