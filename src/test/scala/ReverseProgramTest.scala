/**
  * Created by Mikael on 03/03/2017.
  */

import org.scalatest._
import Matchers.{=== => _, _}
import WebTrees._
import inox._
import inox.evaluators.EvaluationResults
import inox.trees.{not => inoxNot, _}
import inox.trees.dsl._

import scala.reflect.runtime.universe.TypeTag


object Make {
  def apply[A: Constrainable, B](in: Id[A] => (A ~~> B)): (A ~~> B) = in(Id[A]())
}

class ReverseProgramTest extends FunSuite {
  import Constrainable._

  test("Should be able to create a program from scratch") {
    val in = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val t = ReverseProgram.put(in, None, None, None)
    t.toStream.lengthCompare(1) shouldEqual 0
    val Seq((prog, fun)) = t.toSeq
    val evaluator = prog.getEvaluator
    evaluator.eval(FunctionInvocation(fun, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual in
      case m => fail(s"Did not evaluate to $in. Error: $m")
    }
  }
}
