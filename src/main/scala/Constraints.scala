import ImplicitTuples._
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import inox.InoxProgram

import scala.xml.MetaData

import InoxConvertible._

abstract class Tree[LeafValue, NodeValue]
case class Node[LeafValue, NodeValue](left: Tree[LeafValue, NodeValue], value: NodeValue, right: Tree[LeafValue, NodeValue]) extends Tree[LeafValue, NodeValue]
case class Leaf[LeafValue, NodeValue](value: LeafValue) extends Tree[LeafValue, NodeValue]

abstract class GeneralConstraint[A <: GeneralConstraint[A]](protected val formula: Expr,
                                 functions: Map[Identifier, ManualReverse[_, _]])
{
  import inox.solvers._
  import SolverResponses._

  implicit val symbols = {
    Utils.defaultSymbols.withFunctions(ReverseProgram.funDefs)
  }

  // The program
  lazy val context = Context.empty.copy(options = Options(Seq(optSelectedSolvers(Set("smt-cvc4")))))
  lazy val prog = InoxProgram(context, symbols)
  type ThisSolver = solvers.combinators.TimeoutSolver { val program: prog.type }

  def copyWithNewFormula(newFormula: Expr): A

  /** Simplify the formula by replacing String method calls, removing equalities between identifiers */
  def simplify(solutionVars: Set[Variable]): A = {
    val assignments = {
      val TopLevelAnds(conjuncts) = formula
      conjuncts.collect{
        case Equals(v: Variable, t: Literal[_]) => (v -> t)
      }.toMap
    }

    object LeftConstant {
      def unapply(s: inox.trees.Expr): Some[(String, Option[inox.trees.Expr])] = Some(s match {
        case StringConcat(a, b) =>
          LeftConstant.unapply(a).get match {
            case (sa, Some(ea)) => (sa, Some(StringConcat(ea, b)))
            case (sa, None) =>
              LeftConstant.unapply(b).get match {
                case (sb, seb) => (sa + sb, seb)
              }
          }
        case StringLiteral(s) => (s, None)
        case v: Variable => assignments.get(v) match {
          case Some(StringLiteral(s)) => (s, None)
          case _ => ("", Some(v))
        }
        case e => ("", Some(e))
      })
    }

    object RightConstant {
      def unapply(s: inox.trees.Expr): Some[(Option[inox.trees.Expr], String)] = Some(s match {
        case StringConcat(a, b) =>
          RightConstant.unapply(b).get match {
            case (Some(eb), sb) => (Some(StringConcat(a, eb)), sb)
            case (None, sb) =>
              RightConstant.unapply(a).get match {
                case (sea, sa) => (sea, sa + sb)
              }
          }
        case StringLiteral(s) => (None, s)
        case v: Variable => assignments.get(v) match {
          case Some(StringLiteral(s)) => (None, s)
          case _ => (Some(v), "")
        }
        case e => (Some(e), "")
      })
    }

    val toplevelIdentityRemoved = (x: Expr) => x match {
      case TopLevelAnds(ands) =>
        val topEqualities = ands.collect{
          case Equals(v1: Variable, v2: Variable) => (if(!solutionVars(v1)) v1 -> v2 else v2 -> v1):(Expr, Expr)
        }
        val tewi = topEqualities.zipWithIndex
        val topEqualitiesMap = tewi.filter{
          case ((i1, i2), i) => if(tewi.exists{
            case ((j1, j2), j) => j < i && j1 == i2
          }) {
            false // We remove back arrow assignments so that the assignment map is only forward.
          } else true
        }.map(_._1).toMap
        // Prevent loops.
        def transitiveTopEqualities(x: Expr): Option[Expr] = topEqualitiesMap.get(x) match {
          case Some(newVar) => transitiveTopEqualities(newVar).orElse(Some(newVar))
          case None => None
        }
        inox.trees.exprOps.postMap(transitiveTopEqualities _)(x)
      case _ => x
    }
    //Log("#2 " + toplevelIdentityRemoved)
    val removedAndTrue =
      inox.trees.exprOps.postMap{
        case And(exprs) =>
          val trueAnds = exprs.filterNot{ case BooleanLiteral(true) => true case Equals(v, v2) if v == v2 => true case _ => false }
          Some(if(trueAnds.isEmpty) E(true) else
          if(trueAnds.length == 1) trueAnds.head else
            And(trueAnds))
        case _ => None
      } _

    val removeFalseTrue =
      inox.trees.exprOps.postMap{
        case And(exprs) =>
          val isFalse = exprs.exists{
            case Equals(LeftConstant(a, ea), LeftConstant(b, eb)) if !a.startsWith(b) && !b.startsWith(a) => true
            case Equals(RightConstant(ea, a), RightConstant(eb, b)) if !a.endsWith(b) && !b.endsWith(a) => true
            case _ => false
          }
          if(isFalse) Some(BooleanLiteral(false)) else None
        case Or(exprs) =>
          val e = exprs.filter{
            case BooleanLiteral(false) => false
            case _ => true
          }
          Some(or(e: _*))
        case Not(BooleanLiteral(b)) => Some(BooleanLiteral(!b))
        case _ => None
      } _

    val finalFormula = (
      toplevelIdentityRemoved
        andThen removedAndTrue
        andThen removeFalseTrue
      )(formula)

    copyWithNewFormula(finalFormula)
  }

  /** Converts the formula to a stream of conjuncts, each of one being able to yield solutions*/
  def getStreamOfConjuncts(e: Expr): Stream[Seq[Expr]] = {
    e match {
      case And(Seq(a1, a2)) => for {a <- getStreamOfConjuncts(a1); b <- getStreamOfConjuncts(a2); c = a ++ b} yield c
      case And(a1 +: at) => for {a <- getStreamOfConjuncts(a1); b <- getStreamOfConjuncts(And(at)); c = a ++ b} yield c
      case Or(exprs) => exprs.toStream.flatMap(getStreamOfConjuncts)
      case k => Stream(Seq(k))
    }
  }
  /** the leaf values are regular expressions, the node value are function conversions. */
  def splitAtUnknownFunctions(e: Seq[Expr]): Tree[Seq[Expr], Expr] = {
    val (left, valueAndRight) = e.span{
      case k@Equals(FunctionInvocation(identifier, Seq(), Seq(inId, inDefault)), _) if functions contains identifier => false
      case k@Equals(_, FunctionInvocation(identifier, Seq(), Seq(inId, inDefault))) if functions contains identifier => false
      case _ => true
    }
    if(valueAndRight.isEmpty) {
      Leaf(left)
    } else {
      val value +: right = valueAndRight
      if(right.isEmpty) throw new Exception("Could not find any value to recover the split at " + e)
      Node(Leaf(left), value, splitAtUnknownFunctions(right))
    }
  }

  /** Separates the "Maybe(a == b)" statements from the conjunct*/
  def splitMaybe(e: Seq[Expr], notMaybes: Seq[Expr], maybes: Seq[Equals]): (List[Expr], List[Equals]) = {
    e match {
      case Seq() => (notMaybes.reverse.toList, maybes.reverse.toList)
      case FunctionInvocation(Common.maybe, _, Seq(equality@Equals(a, b))) +: tail =>
        splitMaybe(tail, notMaybes, equality +: maybes)
      case a +: tail =>
        splitMaybe(tail, a +: notMaybes, maybes)
    }
  }

  /** An "Equals" here is the inner content of a "Maybe". We want to satisfy most of them if possible.
    * If a combination of maybe is satisfiables with e._1, no sub-combination should be tested.
    * The Int is startToDeleteAt: Int = 0, a way to know the number of Equals from the beginning we should not remove.
    **/
  def maxSMTMaybes(es: Stream[(List[Expr], List[Equals], Int)]): Stream[(ThisSolver, prog.Model)] = {
    if(es.isEmpty) return Stream.empty
    val e = es.head

    /*
       If there are top-level constructs of the form ... && function(in, [inValue]) == out && ...
       and function is registered as manual reversing, we split the constraint into two constraints.
       A = all the conjuncts to the left of this expression (containing in)
       B = all the conjuncts to the right of this expression (containing out)
       We solve B and obtain model M
       We run putManual with the two given arguments to obtain a stream of in values.
       For each in value V, we solve the equations
       A && in == V && M
    */
    val constPart = e._1
    val maybePart = e._2
    val numForceMaybeToKeep = e._3
    Log("The maybes are: " + e._2)

    val solver = prog.getSolver.getNewSolver
    Log("solving " + and(e._1 ++ e._2 : _*))
    solver.assertCnstr(and(e._1 ++ e._2 : _*))
    //Log("#2")
    solver.check(SolverResponses.Model) match {
      case SatWithModel(model) =>
        Log("One solution !")
        val updatedStream = es.filter{ x =>  !x._2.toSet.subsetOf(maybePart.toSet)}

        (solver, model) #:: maxSMTMaybes(updatedStream)
      case m =>
        Log(s"No solution ($m). Removing maybes...")
        maxSMTMaybes(es.tail #::: {
          for {i <- (numForceMaybeToKeep until e._2.length).toStream
               seq = e._2.take(i) ++ e._2.drop(i + 1)
          } yield (constPart, seq, numForceMaybeToKeep)
        })
    }
  }

  /** Given a formula splitted at manual reversing functions (the tree t), returns a stream of solvers and associated modles.*/
  def solveTrees(t: Tree[Seq[Expr], Expr]): Stream[(ThisSolver, prog.Model)] = {
    t match {
      case Leaf(seqExpr) =>
        val (eqs, maybes)  = splitMaybe(seqExpr, Nil, Nil)
        for{ solver <- maxSMTMaybes(Stream((eqs, maybes, 0))) } yield solver
      case Node(Leaf(seqExpr), value, right) =>
        //Log("First we will solve " + right)
        //Log("Then we inverse " + value)
        //Log("And then we solve " + seqExpr)*
        val (function: ManualReverse[_, _], inVar, inDefault, outVar) = value match {
          case k@Equals(FunctionInvocation(identifier, Seq(), Seq(inVar: Variable, inDefault)), b: Variable) => (functions(identifier), inVar, inDefault, b)
          case k@Equals(b: Variable, FunctionInvocation(identifier, Seq(), Seq(inVar: Variable, inDefault))) => (functions(identifier), inVar, inDefault, b)
          case _ => throw new Exception("Cannot reverse this equality: " + value)
        }

        def getInValues[A, B](function: ManualReverse[A, B], outValue: Expr, inDefault: Expr): Iterable[Expr] = {
          val realOutValue = function.constrainableOutput.recoverFrom(outValue)
          val realDefaultValue = optionInoxConvertible(function.constrainableInput).recoverFrom(inDefault)
          val inValues = function.putManual(realOutValue, realDefaultValue)
          inValues.map(function.constrainableInput.produce)
        }

        for { solvermodel <- solveTrees(right)
              model <- getStreamOfSolutions(outVar, solvermodel)
              outValue = model.vars(outVar.toVal  : inox.trees.ValDef)
              inValue <- getInValues(function, outValue, inDefault)
              newSeqExpr = (seqExpr :+ Equals(inVar, inValue)) ++ model.vars.map{ case (v, e) => Equals(v.toVariable, e) }
              //_ = Log("Solving this :" + newSeqExpr)
              (eqs, maybes)  = splitMaybe(newSeqExpr, Nil, Nil)
              //_ = Log("Solving maybe:" + x)
              solver <- maxSMTMaybes(Stream((eqs, maybes, 0)))
        } yield {
          solver
        }

      case _ => throw new Exception("[Internal error] Does not support this shape of tree : " + t)
    }
  }

  /** Given an input variable, returns a stream of models with valuations of this variable */
  def getStreamOfSolutions(inputVar: Variable, e: (ThisSolver, prog.Model)): Stream[prog.Model] = {
    val solver = e._1
    val solutionInit = e._2
    //Log(s"Looking for $inputVar in $solutionInit")
    val solutionInitExpr: Expr = solutionInit.vars(inputVar.toVal  : inox.trees.ValDef)
    //Log("Found solution " + solutionInitExpr)
    //Log("Supposing " + !(inputVar === solutionInit))

    def otherSolutions(prevSol: inox.trees.Expr): Stream[prog.Model] = {
      solver.check(SolverResponses.Model) match {
        case SatWithModel(model) =>
          // We are going to plug in the maximum number of equals possible until it breaks.
          val solution: Expr = model.vars(inputVar.toVal  : inox.trees.ValDef)
          //Log("Found solution " + solution)
          if (prevSol == solution) Stream.empty else {
            model #:: {
              //Log("Supposing " + !(inputVar === solution))
              solver.assertCnstr(!(inputVar === solution))
              otherSolutions(solution)
            }
          }
        case _ =>
          //Log("No more solutions")
          Stream.empty[prog.Model]
      }
    }
    solutionInit #:: {
      solver.assertCnstr(!(inputVar === solutionInitExpr))
      otherSolutions(solutionInitExpr)
    }
  }

  /** Returns a stream of solutions satisfying the constraint */
  def toStreamOfInoxExpr(solutionVar: inox.trees.Variable): Stream[Expr] = {
    val simplified = simplify(Set(solutionVar)).formula

    Log(s"######## Converting this formula to stream of solutions for $solutionVar ######\n" + simplified)


    // The stream of conjuncts splitted with the maybes.
    for {a <- getStreamOfConjuncts(simplified)
         _ = Log("Solving conjunct : " + a)
         splitted = splitAtUnknownFunctions(a)
         solver <- solveTrees(splitted)
         modelInox <- getStreamOfSolutions(solutionVar, solver)
         solutionInox = modelInox.vars(solutionVar.toVal: inox.trees.ValDef)
    }
      yield {
        solutionInox
      }
  }
}

/** A wrapper around an inox Expr which can enumerate solutions*/
case class Constraint[A: InoxConvertible](protected val _formula: Expr,
                                          functions: Map[Identifier, ManualReverse[_, _]] = Map())
  extends GeneralConstraint[Constraint[A]](_formula, functions) {
  /** Adds a new assignment to this constraint */
  def apply[A: InoxConvertible](tuple: (inox.trees.Variable, A)) = this && tuple._1 === inoxExprOf[A](tuple._2)

  /** Adds a new conjunct to this constraint */
  def &&(b: Expr) = Constraint[A](formula && b, functions)

  /** Adds a new conjunct to this constraint */
  def &&[B: InoxConvertible](b: Constraint[B]): Constraint[A] = Constraint[A](formula && b.formula, functions ++ b.functions)
  def <&&[B: InoxConvertible](b: Constraint[B]): Constraint[B] = Constraint[B](formula && b.formula, functions ++ b.functions)

  import inox.solvers._
  import SolverResponses._

  def copyWithNewFormula(newFormula: Expr): Constraint[A] = {
    Constraint[A](newFormula, functions)
  }

  /** Returns a stream of solutions satisfying the constraint */
  def toStream(solutionVar: inox.trees.Variable): Stream[A] = {
    toStreamOfInoxExpr(solutionVar).map(exprOfInox[A] _)
  }
}

case class InoxConstraint(protected val _formula: Expr, functions: Map[Identifier, ManualReverse[_, _]] = Map())
extends GeneralConstraint[InoxConstraint](_formula, functions)
{
  def copyWithNewFormula(newFormula: Expr) = this.copy(_formula = newFormula)

}