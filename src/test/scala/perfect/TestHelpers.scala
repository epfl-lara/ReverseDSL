package perfect
import legacy._

/**
  * Created by Mikael on 09/03/2017.
  */
import org.scalatest._
import matchers._
import Matchers.{=== => _, _}
import Utils._
import WebTrees._
import inox._
import inox.evaluators.EvaluationResults
import inox.trees.{not => inoxNot, _}
import inox.trees.dsl._

import scala.reflect.runtime.universe.TypeTag


/** Mixin for tests repairing programs */
trait TestHelpers extends InoxConvertible.conversions { self: FunSuite =>
  import InoxConvertible._
  import StringConcatExtended._


  implicit class Obtainable(body: Expr) {
    def repairFrom(e: ProgramFormula) = repairProgram(body, e)
    def shouldProduce(e: Expr) = checkProg(e, body)
  }

  private def mkProg(funDef: FunDef) = {
    InoxProgram(
      ReverseProgram.context,
      funDef::lenses.Lenses.funDefs, allConstructors
    )
  }

  import Utils.AugmentedStream
  private def sortStreamByDistance(s: Stream[Expr], num: Int, init: Expr) = {
    s.sortFirstElements(num, (x: Expr) => {
      DistanceExpr.distance(x, init)// /: Log.prefix(s"distance(${x.getBody}, $init)=")
    })
  }

  implicit def knownToKnown(in: Map[Variable, InoxProgramUpdater.KnownValue]): Map[Variable, KnownValue] = {
    in.mapValues{
      case InoxProgramUpdater.StrongValue(s) => StrongValue(s)
      case InoxProgramUpdater.OriginalValue(s) => OriginalValue(s)
      case InoxProgramUpdater.InsertVariable(s) => InsertVariable(s)
      case InoxProgramUpdater.AllValues => AllValues
    }
  }
  implicit def knownFromKnown(in: Map[Variable, KnownValue]): Map[Variable, InoxProgramUpdater.KnownValue] = {
    in.mapValues{
      case StrongValue(s) => InoxProgramUpdater.StrongValue(s)
      case OriginalValue(s) => InoxProgramUpdater.OriginalValue(s)
      case InsertVariable(s) => InoxProgramUpdater.InsertVariable(s)
      case AllValues => InoxProgramUpdater.AllValues
    }
  }

  implicit def formulaToCont(in: Formula): InoxProgramUpdater.Cont = InoxProgramUpdater.Cont(in.known, in.constraints)
  implicit def pfToContExp(in: ProgramFormula): InoxProgramUpdater.ContExp = InoxProgramUpdater.ContExp(in.expr, in.formula)
  implicit def contToFormula(in: InoxProgramUpdater.Cont): Formula = Formula(in.known, in.constraints)
  implicit def ContExpToPF(in: InoxProgramUpdater.ContExp): ProgramFormula = ProgramFormula(in.exp, in.context)


  val reverser = InoxProgramUpdater
    ReverseProgram

  /** Returns all the solution, with the first lookInManyFirstSolutions being sorted */
  def repairProgramList(pf: Expr, expected2: ProgramFormula, lookInManyFirstSolutions: Int): Stream[Expr] = {
    val progfuns2 = reverser.put(Some(pf), expected2)
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
    val progfuns2 = reverser.put(None, ProgramFormula(expected2))
    progfuns2.toStream.lengthCompare(1) should be >= 0
    progfuns2.head
  }

  def eval(e: Expr): Expr = {
    if(reverser == ReverseProgram) {
      val symbols = Utils.defaultSymbols.withFunctions(lenses.Lenses.funDefs)

      val funDef = mkFunDef(main)()(_ => (Seq(), e.getType(symbols), _ => e))
      (mkProg(funDef), funDef.id)

      val prog = InoxProgram(
        ReverseProgram.context,
        funDef :: lenses.Lenses.funDefs, allConstructors
      )

      ReverseProgram.LambdaPreservingEvaluator(prog).eval(FunctionInvocation(main, Seq(), Seq())) match {
        case EvaluationResults.Successful(e) => e
        case m => fail(s"Error while evaluating ${e}: $m")
      }
    } else {
      implicit val symbols: InoxProgramUpdater.Symbols = Utils.defaultSymbols.withFunctions(lenses.Lenses.funDefs)
      InoxProgramUpdater.eval(e).fold(x => x, msg => fail(s"Error while evaluating ${e}: $msg"))
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

