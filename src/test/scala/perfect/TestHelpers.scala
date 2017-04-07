package perfect
import legacy._

/**
  * Created by Mikael on 09/03/2017.
  */
import org.scalatest._
import matchers._
import Matchers.{=== => _, _}
import ReverseProgram.FunctionEntry
import Utils._
import WebTrees._
import inox._
import inox.evaluators.EvaluationResults
import inox.trees.{not => inoxNot, _}
import inox.trees.dsl._

import scala.reflect.runtime.universe.TypeTag


/** Mixin for tests repairing programs */
trait TestHelpers extends InoxConvertible.conversions {
  import InoxConvertible._
  import StringConcatExtended._


  implicit class Obtainable(body: Expr) {
    def repairFrom(e: ProgramFormula) = repairProgram(body, e)
    def shouldProduce(e: Expr) = checkProg(e, body)
  }

  private def mkProg(funDef: FunDef) = {
    InoxProgram(
      ReverseProgram.context,
      funDef::ReverseProgram.funDefs, allConstructors
    )
  }

  import Utils.AugmentedStream
  private def sortStreamByDistance(s: Stream[Expr], num: Int, init: Expr) = {
    s.sortFirstElements(num, (x: Expr) => {
      DistanceExpr.distance(x, init)// /: Log.prefix(s"distance(${x.getBody}, $init)=")
    })
  }

  /** Returns all the solution, with the first lookInManyFirstSolutions being sorted */
  def repairProgramList(pf: Expr, expected2: ProgramFormula, lookInManyFirstSolutions: Int): Stream[Expr] = {
    val progfuns2 = ReverseProgram.put(expected2, Some(pf))
    progfuns2.lengthCompare(0) should be > 0
    val initialValue = pf
    val sorted = sortStreamByDistance(progfuns2, lookInManyFirstSolutions, initialValue)
    if(Log.activate) {
      sorted.take(lookInManyFirstSolutions).toList.zipWithIndex.foreach { case (sol, i) =>
        Log(s"Solution $i:" + sol)
      }
    }
    sorted
  }

  def repairProgram(pf: Expr, expected2: ProgramFormula, lookInManyFirstSolutions: Int = 1): Expr = {
    val res =
    repairProgramList(pf, expected2, lookInManyFirstSolutions).head
    println("### repair:\n" + pf +"\n###by outputing: " + expected2 + " gives:\n" + res + "\n###")
    res
  }

  def generateProgram(expected2: Expr): Expr = {
    val progfuns2 = ReverseProgram.put(ProgramFormula(expected2), None)
    progfuns2.toStream.lengthCompare(1) should be >= 0
    progfuns2.head
  }

  def eval(e: Expr): Expr = {
    val symbols = Utils.defaultSymbols.withFunctions(ReverseProgram.funDefs)

    val funDef = mkFunDef(main)()(_ => (Seq(), e.getType(symbols), _ => e))
    (mkProg(funDef), funDef.id)

    val prog = InoxProgram(
      ReverseProgram.context,
      funDef::ReverseProgram.funDefs, allConstructors
    )

    ReverseProgram.LambdaPreservingEvaluator(prog).eval(FunctionInvocation(main, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => e
      case m => fail(s"Error while evaluating ${e}: $m")
    }
  }

  def checkProg(expected1: Expr, program: Expr): Expr = {
    eval(program) shouldEqual expected1
    program
  }

  protected def isVarIn(id: Identifier, body: inox.trees.Expr): Boolean = {
    inox.trees.exprOps.exists {
      case v: Variable => v.id == id
      case _ => false
    }(body)
  }

  protected def countVarIn(id: Identifier, body: inox.trees.Expr): Int = {
    inox.trees.exprOps.count {
      case v: Variable if v.id == id => 1
      case _ => 0
    }(body)
  }

  val main = FreshIdentifier("main")
}

