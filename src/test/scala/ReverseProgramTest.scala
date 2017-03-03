/**
  * Created by Mikael on 03/03/2017.
  */

import org.scalatest._
import Matchers.{=== => _, _}
import ReverseProgram.FunctionEntry
import Utils._
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

  implicit def toStringLiteral(s: String): StringLiteral = StringLiteral(s)

  test("Create a program from scratch") {
    val out = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val progfuns = ReverseProgram.put(out, None, None, None)
    progfuns.toStream.lengthCompare(1) shouldEqual 0
    val Seq((prog, fun)) = progfuns.toSeq
    val evaluator = prog.getEvaluator
    evaluator.eval(FunctionInvocation(fun, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual out
      case m => fail(s"Did not evaluate to $out. Error: $m")
    }
  }

  test("Change a constant output to another") {
    val out = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val (prog, fun) = ReverseProgram.put(out, None, None, None).head
    val out2 = Element("pre", WebElement(TextNode("Hello code"))::Nil)
    val (prog2, fun2) = ReverseProgram.put(out2, None, None, Some((prog, fun))).head
    val evaluator = prog2.getEvaluator
    evaluator.eval(FunctionInvocation(fun2, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual out2
      case m => fail(s"Did not evaluate to $out. Error: $m")
    }
  }

  test("Variable assigment keeps the shape") {
    val main = FreshIdentifier("main")
    val tmpVar = variable[String]("text")
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val funDef = mkFunDef(main)()(_ => (Seq(), inoxTypeOf[Element], _ =>
      let(tmpVar.toVal, StringLiteral("Hello world"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]())
      )
    ))
    val prog = InoxProgram(
      ReverseProgram.context,
      Seq(funDef), allConstructors
    )
    prog.getEvaluator.eval(FunctionInvocation(funDef.id, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual expected1
      case m => fail(s"Did not evaluate to $expected1. Error: $m")
    }
    val expected2 = Element("div", WebElement(TextNode("We are the children"))::Nil)

    val progfuns2 = ReverseProgram.put(expected2, None, None, Some((prog, funDef.id)))

    progfuns2.toStream.lengthCompare(1) shouldEqual 0

    val (prog2, funId2) = progfuns2.head
    prog2.getEvaluator.eval(FunctionInvocation(funId2, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual expected2
      case m => fail(s"Did not evaluate to $expected2. Error: $m")
    }

    // testing the shape.
    prog2.symbols.functions.get(funId2) match {
      case None => fail("???")
      case Some(funDef) => funDef.fullBody match {
        case l: Let => // ok
        case m => fail(s"eXpected let, got $m")
      }
    }
  }

  test("Variable assigment used twice") {
    val main = FreshIdentifier("main")
    val tmpVar = variable[String]("text")
    val initial   = Element("div", WebElement(TextNode("red"))::Nil,  Nil, WebStyle("color", "red")::Nil)
    val out2      = Element("div", WebElement(TextNode("blue"))::Nil, Nil, WebStyle("color", "red")::Nil)
    val expected2 = Element("div", WebElement(TextNode("blue"))::Nil, Nil, WebStyle("color", "blue")::Nil)

    val funDef = mkFunDef(main)()(_ => (Seq(), inoxTypeOf[Element], _ =>
      let(tmpVar.toVal, StringLiteral("red"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle](_WebStyle("color", v)))
      )
    ))
    val prog = InoxProgram(
      ReverseProgram.context,
      Seq(funDef), allConstructors
    )
    prog.getEvaluator.eval(FunctionInvocation(funDef.id, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual initial
      case m => fail(s"Did not evaluate to $initial. Error: $m")
    }

    val progfuns2 = ReverseProgram.put(out2, None, None, Some((prog, funDef.id)))

    progfuns2.toStream.lengthCompare(1) shouldEqual 0

    val (prog2, funId2) = progfuns2.head
    prog2.getEvaluator.eval(FunctionInvocation(funId2, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual expected2
      case m => fail(s"Did not evaluate to $expected2. Error: $m")
    }
  }

  test("Variable assigment same, outer structure") {
    val main = FreshIdentifier("main")
    val tmpVar = variable[String]("text")
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val funDef = mkFunDef(main)()(_ => (Seq(), inoxTypeOf[Element], _ =>
      let(tmpVar.toVal, StringLiteral("Hello world"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]())
      )
    ))
    val prog = InoxProgram(
      ReverseProgram.context,
      Seq(funDef), allConstructors
    )
    prog.getEvaluator.eval(FunctionInvocation(funDef.id, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual expected1
      case m => fail(s"Did not evaluate to $expected1. Error: $m")
    }
    val expected2 = Element("div", WebElement(TextNode("We are the children"))::Nil)

    val progfuns2 = ReverseProgram.put(expected2, None, None, Some((prog, funDef.id)))

    progfuns2.toStream.lengthCompare(1) shouldEqual 0

    val (prog2, funId2) = progfuns2.head
    prog2.getEvaluator.eval(FunctionInvocation(funId2, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual expected2
      case m => fail(s"Did not evaluate to $expected2. Error: $m")
    }

    // testing the shape.
    prog2.symbols.functions.get(funId2) match {
      case None => fail("???")
      case Some(funDef) => funDef.fullBody match {
        case l: Let => // ok
        case m => fail(s"eXpected let, got $m")
      }
    }
  }

  val main = FreshIdentifier("main")
  val build = Variable(FreshIdentifier("build"), FunctionType(Seq(inoxTypeOf[String]), inoxTypeOf[Element]), Set())
  val v = variable[String]("v")
  val lambda = Lambda(Seq(v.toVal),
    _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]()))

  test("Change a lambda's argument") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val funDef = mkFunDef(main)()(_ => (Seq(), inoxTypeOf[Element], _ =>
      let(build.toVal, lambda)(b =>
      Application(b, Seq("Hello world"))
      )
    ))
    val prog = InoxProgram(ReverseProgram.context, Seq(funDef), allConstructors)
    prog.getEvaluator.eval(FunctionInvocation(funDef.id, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual expected1
      case m => fail(s"Did not evaluate to $expected1. Error: $m")
    }
    val expected2 = Element("div", WebElement(TextNode("We are the children"))::Nil)

    val progfuns2 = ReverseProgram.put(expected2, None, None, Some((prog, funDef.id)))
    progfuns2.toStream.lengthCompare(1) shouldEqual 0

    val (prog2, funId2) = progfuns2.head
    prog2.getEvaluator.eval(FunctionInvocation(funId2, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual expected2
      case m => fail(s"Did not evaluate to $expected2. Error: $m")
    }

    // testing the shape.
    prog2.symbols.functions.get(funId2) match {
      case None => fail("???")
      case Some(funDef) => funDef.fullBody match {
        case Let(_, _, Application(_, Seq(StringLiteral(s)))) => s shouldEqual "We are the children"
        case m => fail(s"eXpected 'We are the children' in application, got $m")
      }
    }
  }

  test("Change a lambda's shape by wrapping an element") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val funDef = mkFunDef(main)()(_ => (Seq(), inoxTypeOf[Element], _ =>
      let(build.toVal, lambda)(b =>
      Application(b, Seq("Hello world"))
      )
    ))
    val prog = InoxProgram(
      ReverseProgram.context,
      Seq(funDef), allConstructors
    )
    val expected2 = Element("div", WebElement(Element("b", WebElement(TextNode("Hello world"))::Nil))::Nil)

    val progfuns2 = ReverseProgram.put(expected2, None, None, Some((prog, funDef.id)))

    progfuns2.toStream.lengthCompare(1) shouldEqual 0

    val (prog2, funId2) = progfuns2.head
    prog2.getEvaluator.eval(FunctionInvocation(funId2, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual expected2
      case m => fail(s"Did not evaluate to $expected2. Error: $m")
    }

    // testing that the lambda changed but keeps the variable.
    prog2.symbols.functions.get(funId2) match {
      case None => fail("???")
      case Some(funDef) => funDef.fullBody match {
        case Let(_, newLambda@Lambda(Seq(v2), body), Application(_, Seq(StringLiteral(_)))) =>
          assert(inox.trees.exprOps.exists{
            case v3:Variable => v2 == v2
            case _ => false
          }(body), s"There was no variable $v in the given lambda: $newLambda")

        case m => fail(s"eXpected a let-lambda-application', got $m")
      }
    }
  }

  test("Change a lambda's shape by inserting a constant element") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val funDef = mkFunDef(main)()(_ => (Seq(), inoxTypeOf[Element], _ =>
      let(build.toVal, lambda)(b =>
        Application(b, Seq("Hello world"))
      )
    ))
    val prog = InoxProgram(
      ReverseProgram.context,
      Seq(funDef), allConstructors
    )
    val expected2 = Element("div", WebElement(Element("br"))::WebElement(TextNode("Hello world"))::Nil)

    val progfuns2 = ReverseProgram.put(expected2, None, None, Some((prog, funDef.id)))

    progfuns2.toStream.lengthCompare(1) shouldEqual 0

    val (prog2, funId2) = progfuns2.head
    prog2.getEvaluator.eval(FunctionInvocation(funId2, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual expected2
      case m => fail(s"Did not evaluate to $expected2. Error: $m")
    }

    // testing that the lambda changed but keeps the variable.
    prog2.symbols.functions.get(funId2) match {
      case None => fail("???")
      case Some(funDef) => funDef.fullBody match {
        case Let(_, newLambda@Lambda(Seq(v2), body), Application(_, Seq(StringLiteral(_)))) =>
          assert(inox.trees.exprOps.exists{
            case v3:Variable => v2 == v2
            case _ => false
          }(body), s"There was no variable $v in the given lambda: $newLambda")

        case m => fail(s"eXpected a let-lambda-application', got $m")
      }
    }
  }

  /* Add tests for:
     change in the shape of the way the program is built.
     change in a sub-function
     List mapping, flatten, flatmap, filter.


    */
}
