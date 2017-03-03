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

  def mkProg(funDef: FunDef) = InoxProgram(
    ReverseProgram.context,
    Seq(funDef), allConstructors
  )

  def repairProgram[A: Constrainable](funDef: inox.trees.dsl.trees.FunDef, prog: InoxProgram, expected2: A) = {
    val progfuns2 = ReverseProgram.put(expected2, None, None, Some((prog, funDef.id)))
    progfuns2.toStream.lengthCompare(1) should be >= 0
    val (prog2, funId2) = progfuns2.head
    (prog2, funId2)
  }
  def generateProgram[A: Constrainable](expected2: A) = {
    val progfuns2 = ReverseProgram.put(expected2, None, None, None)
    progfuns2.toStream.lengthCompare(1) should be >= 0
    val (prog2, funId2) = progfuns2.head
    (prog2, funId2)
  }

  def checkProg[A: Constrainable](expected1: A, funDefId: Identifier, prog: InoxProgram) = {
    prog.getEvaluator.eval(FunctionInvocation(funDefId, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[A](e) shouldEqual expected1
      case m => fail(s"Did not evaluate to $expected1. Error: $m")
    }
  }

  def function(returnType: Type)(body: Expr) = mkFunDef(main)()(_ => (Seq(), returnType, _ => body))

  val main = FreshIdentifier("main")
  val build = Variable(FreshIdentifier("build"), FunctionType(Seq(inoxTypeOf[String]), inoxTypeOf[Element]), Set())
  val v = variable[String]("v")
  val vText = variable[String]("text")

  test("Create a program from scratch") {
    val out = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val (prog, fun) = generateProgram(out)
    checkProg(out, fun, prog)
  }

  test("Change a constant output to another") {
    val out = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val (prog, fun) = ReverseProgram.put(out, None, None, None).head
    val out2 = Element("pre", WebElement(TextNode("Hello code"))::Nil)
    val (prog2, fun2) = ReverseProgram.put(out2, None, None, Some((prog, fun))).head
    checkProg(out2, fun2, prog2)
  }

  test("Variable assigment keeps the shape") {
    val expected1 = "Hello world"
    val expected2 = "We are the children"

    val funDef = function(inoxTypeOf[String])(
      let(vText.toVal, "Hello world")(v => v)
    )
    val prog = mkProg(funDef)
    checkProg(expected1, funDef.id, prog)

    val (prog2, funId2) = repairProgram(funDef, prog, expected2)
    checkProg(expected2, funId2, prog2)

    // testing the shape.
    prog2.symbols.functions.get(funId2) match {
      case None => fail("???")
      case Some(funDef) => funDef.fullBody match {
        case l@Let(vd, expr, body) =>
          val v = vd.toVariable
          if(!inox.trees.exprOps.exists{
            case v2:Variable => v2.id == v.id
            case _ => false
          }(body)) fail(s"There was no use of the variable $v in the given let-expression: $l")

        case m => fail(s"eXpected let, got $m")
      }
    }
  }

  test("Variable assigment keeps the shape if deep embedded") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(TextNode("We are the children"))::Nil)

    val funDef = function(inoxTypeOf[Element])(
      let(vText.toVal, StringLiteral("Hello world"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]())
      )
    )
    val prog = mkProg(funDef)
    prog.getEvaluator.eval(FunctionInvocation(funDef.id, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual expected1
      case m => fail(s"Did not evaluate to $expected1. Error: $m")
    }

    val (prog2: InoxProgram, funId2: FunctionEntry) = repairProgram(funDef, prog, expected2)
    checkProg(expected2, funId2, prog2)

    // testing the shape.
    prog2.symbols.functions.get(funId2) match {
      case None => fail("???")
      case Some(funDef) => funDef.fullBody match {
        case l@Let(vd, expr, body) =>
          val v = vd.toVariable
          if(!inox.trees.exprOps.exists{
            case v2:Variable => v2.id == v.id
            case _ => false
          }(body)) fail(s"There was no use of the variable $v in the given let-expression: $l")

        case m => fail(s"eXpected let, got $m")
      }
    }
  }

  test("2 Variable assigments deep embedded") {
    val main = FreshIdentifier("main")
    val text = variable[String]("text")
    val attr = variable[WebAttribute]("attr")
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil, WebAttribute("class", "bgfont")::Nil)
    val expected2 = Element("div", WebElement(TextNode("We are the children"))::Nil, WebAttribute("class", "bgfontbig")::Nil)

    val funDef = function(inoxTypeOf[Element])(
      let(text.toVal, "Hello world")(v =>
        let(attr.toVal, _WebAttribute("class", "bgfont"))(a =>
          _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](a), _List[WebStyle]())
        )
      )
    )
    val prog = mkProg(funDef)
    checkProg(expected1, funDef.id, prog)

    val (prog2: InoxProgram, funId2: FunctionEntry) = repairProgram(funDef, prog, expected2)
    checkProg(expected2, funId2, prog2)

    // testing the shape.
    prog2.symbols.functions.get(funId2) match {
      case None => fail("???")
      case Some(funDef) => funDef.fullBody match {
        case l@Let(vd, expr, l2@Let(vd2, expr2, body)) =>
          val v = vd.toVariable
          if(!inox.trees.exprOps.exists{
            case v2:Variable => v2.id == v.id
            case _ => false
          }(body)) fail(s"There was no use of the variable $v in the given let-expression: $l")
          val vv = vd2.toVariable
          if(!inox.trees.exprOps.exists{
            case v2:Variable => v2.id == vv.id
            case _ => false
          }(body)) fail(s"There was no use of the variable $v in the given let-expression: $l")

        case m => fail(s"eXpected let, got $m")
      }
    }
  }

  test("Variable assigment used twice") {
    val initial   = Element("div", WebElement(TextNode("red"))::Nil,  Nil, WebStyle("color", "red")::Nil)
    val out2      = Element("div", WebElement(TextNode("blue"))::Nil, Nil, WebStyle("color", "red")::Nil)
    val expected2 = Element("div", WebElement(TextNode("blue"))::Nil, Nil, WebStyle("color", "blue")::Nil)

    val funDef = function(inoxTypeOf[Element])(
      let(vText.toVal, StringLiteral("red"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle](_WebStyle("color", v)))
      )
    )
    val prog = mkProg(funDef)
    checkProg[Element](initial, funDef.id, prog)

    val (prog2: InoxProgram, funId2: FunctionEntry) = repairProgram(funDef, prog, out2)
    checkProg(expected2, funId2, prog2)
  }

  test("Variable assigment same, outer structure") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(Element("b", WebElement(TextNode("Hello world"))::Nil))::Nil)

    val funDef = function(inoxTypeOf[Element])(
      let(vText.toVal, StringLiteral("Hello world"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]())
      )
    )
    val prog = mkProg(funDef)
    checkProg[Element](expected1, funDef.id, prog)

    val (prog2: InoxProgram, funId2: FunctionEntry) = repairProgram(funDef, prog, expected2)
    checkProg(expected2, funId2, prog2)

    // testing the shape.
    prog2.symbols.functions.get(funId2) match {
      case None => fail("???")
      case Some(funDef) => funDef.fullBody match {
        case l@Let(vd, expr, body) =>
          println(l)
          val v = vd.toVariable
          if(!inox.trees.exprOps.exists{
            case v2:Variable => v2.id == v.id
            case _ => false
          }(body)) fail(s"There was no use of the variable $v in the given let-expression: $l")
        case m => fail(s"eXpected let, got $m")
      }
    }
  }

  val lambda = Lambda(Seq(v.toVal),
    _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]()))

  test("Change a lambda's argument") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val funDef = function(inoxTypeOf[Element])(
      let(build.toVal, lambda)(b =>
      Application(b, Seq("Hello world"))
      )
    )
    val prog = InoxProgram(ReverseProgram.context, Seq(funDef), allConstructors)
    prog.getEvaluator.eval(FunctionInvocation(funDef.id, Seq(), Seq())) match {
      case EvaluationResults.Successful(e) => exprOfInox[Element](e) shouldEqual expected1
      case m => fail(s"Did not evaluate to $expected1. Error: $m")
    }
    val expected2 = Element("div", WebElement(TextNode("We are the children"))::Nil)

    val (prog2: InoxProgram, funId2: FunctionEntry) = repairProgram(funDef, prog, expected2)
    checkProg[Element](expected2, funId2, prog2)

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
    val funDef = function(inoxTypeOf[Element])(
      let(build.toVal, lambda)(b =>
      Application(b, Seq("Hello world"))
      )
    )
    val prog = mkProg(funDef)
    val expected2 = Element("div", WebElement(Element("b", WebElement(TextNode("Hello world"))::Nil))::Nil)

    val (prog2: InoxProgram, funId2: FunctionEntry) = repairProgram(funDef, prog, expected2)


    checkProg(expected2, funId2, prog2)

    // testing that the lambda changed but keeps the variable.
    prog2.symbols.functions.get(funId2) match {
      case None => fail("???")
      case Some(funDef) => funDef.fullBody match {
        case Let(_, newLambda@Lambda(Seq(v2), body), Application(_, Seq(StringLiteral(_)))) =>
          if(!inox.trees.exprOps.exists{
            case v3:Variable => v2 == v2
            case _ => false
          }(body)) fail(s"There was no variable $v in the given lambda: $newLambda")

        case m => fail(s"eXpected a let-lambda-application', got $m")
      }
    }
  }

  test("Change a lambda's shape by inserting a constant element") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(Element("br"))::WebElement(TextNode("Hello world"))::Nil)

    val funDef = function(inoxTypeOf[Element])(
      let(build.toVal, lambda)(b =>
        Application(b, Seq("Hello world"))
      )
    )
    val prog = mkProg(funDef)

    val (prog2: InoxProgram, funId2: FunctionEntry) = repairProgram(funDef, prog, expected2)

    checkProg(expected2, funId2, prog2)

    // testing that the lambda changed but keeps the variable.
    prog2.symbols.functions.get(funId2) match {
      case None => fail("???")
      case Some(funDef) => funDef.fullBody match {
        case Let(_, newLambda@Lambda(Seq(v2), body), Application(_, Seq(StringLiteral(_)))) =>
          if(!inox.trees.exprOps.exists{
            case v3:Variable => v2 == v2
            case _ => false
          }(body)) fail(s"There was no variable $v in the given lambda: $newLambda")

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
