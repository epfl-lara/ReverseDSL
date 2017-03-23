package legacy

import inox.Identifier
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import perfect.{GeneralConstraint, InoxConvertible}
import perfect.InoxConvertible.{exprOfInox, inoxExprOf}
import perfect.ManualReverse

/**
  * Created by Mikael on 23/03/2017.
  */

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