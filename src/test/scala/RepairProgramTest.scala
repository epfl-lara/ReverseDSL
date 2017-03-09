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
import sun.swing.SwingUtilities2.RepaintListener

import scala.reflect.runtime.universe.TypeTag

object Make {
  def apply[A: Constrainable, B](in: Id[A] => (A ~~> B)): (A ~~> B) = in(Id[A]())
}

/** Mixin for tests repairing programs */
trait RepairProgramTest {
  import Constrainable._

  type PFun = (InoxProgram, Identifier)

  implicit def toExpr[A : Constrainable](e: A): Expr = inoxExprOf[A](e)

  implicit class Obtainable(pf: (inox.InoxProgram, Identifier)) {
    @inline private def matchFunDef(test: FunDef => Unit) = pf._1.symbols.functions.get(pf._2) match {
      case Some(funDef) => test(funDef)
      case None => fail(s"There was no such function ${pf._2} in program:\n${pf._1}")
    }
    def matchBody(test: PartialFunction[Expr,Unit]) = matchFunDef{ funDef =>
      val body = funDef.fullBody
      if(test.isDefinedAt(body)) {
        test(body)
      } else {
        fail(s"Unexpected shape:\n$body")
      }
    }
    def getBody: Expr = {
      pf._1.symbols.functions.get(pf._2).map(_.fullBody).getOrElse(throw new Exception(s"Non-existent function in program $pf"))
    }
  }

  def mkProg(funDef: FunDef) = {
    InoxProgram(
      ReverseProgram.context,
      Seq(funDef), allConstructors
    )
  }

  def sortStreamByDistance(s: Stream[PFun], num: Int, init: Expr) = {
    s.take(num).sortBy((x: PFun) => Distances.distance(x.getBody, init)) #::: s.drop(num)
  }

  /*def repairProgram[A: Constrainable](
       funDef: inox.trees.dsl.trees.FunDef, prog: InoxProgram, expected2: A,
       lookInManyFirstSolutions: Int = 1): PFun = {
    repairProgram(funDef, prog, inoxExprOf[A](expected2),
      lookInManyFirstSolutions)
  }
*/
  def repairProgram(
      funDef: inox.trees.dsl.trees.FunDef, prog: InoxProgram, expected2: Expr,
      lookInManyFirstSolutions: Int = 1): PFun = {
    val progfuns2 = ReverseProgram.put(expected2, None, None, Some((prog, funDef.id))).toStream
    progfuns2.lengthCompare(1) should be >= 0
    val initialValue = (prog, funDef.id).getBody
    val sorted = sortStreamByDistance(progfuns2, lookInManyFirstSolutions, initialValue)
    println("Solutions: by order")
    sorted.take(lookInManyFirstSolutions).foreach{ sol =>
      println(sol.getBody)
    }
    sorted.head
  }
  def generateProgram[A: Constrainable](expected2: A) = {
    val progfuns2 = ReverseProgram.put(expected2, None, None, None)
    progfuns2.toStream.lengthCompare(1) should be >= 0
    val (prog2, funId2) = progfuns2.head
    (prog2, funId2)
  }

  def checkProg[A: Constrainable](expected1: A, prog: InoxProgram, funDefId: Identifier): (InoxProgram, Identifier) = {
    prog.getEvaluator.eval(FunctionInvocation(funDefId, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[A](e) shouldEqual expected1
      case m => fail(s"Did not evaluate to $expected1. Error: $m")
    }
    (prog, funDefId)
  }

  def checkProg[A: Constrainable](expected1: A, progfun: (InoxProgram, Identifier)): (InoxProgram, Identifier) = {
    checkProg(expected1, progfun._1, progfun._2)
  }


  protected def isVarIn(id: Identifier, body: inox.trees.Expr) = {
    inox.trees.exprOps.exists {
      case v: Variable => v.id == id
      case _ => false
    }(body)
  }

  val main = FreshIdentifier("main")

  protected def function(body: Expr)(returnType: Type) = mkFunDef(main)()(_ => (Seq(), returnType, _ => body))
}

