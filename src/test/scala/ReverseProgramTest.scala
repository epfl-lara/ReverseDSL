/**
  * Created by Mikael on 03/03/2017.
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

  implicit class Obtainable(p: inox.InoxProgram) {
    def get(f: Identifier) = new {
      def andMatch(test: FunDef => Unit) = p.symbols.functions.get(f) match {
        case Some(funDef) => test(funDef)
        case None => fail("???")
      }
    }
    def getBodyOf(f: Identifier) = new {
      def andMatch(test: PartialFunction[Expr,Unit]) = get(f).andMatch{ funDef =>
        val body = funDef.fullBody
        if(test.isDefinedAt(body)) {
          test(body)
        } else {
          fail(s"Unexpected shape:\n$body")
        }
      }
    }
  }

  private def isVarIn(id: Identifier, body: inox.trees.Expr) = {
    inox.trees.exprOps.exists {
      case v: Variable => v.id == id
      case _ => false
    }(body)
  }

  def function(body: Expr)(returnType: Type) = mkFunDef(main)()(_ => (Seq(), returnType, _ => body))

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
    val out  = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val out2 = Element("pre", WebElement(TextNode("Hello code"))::Nil)
    val (prog, fun) = ReverseProgram.put(out, None, None, None).head
    val (prog2, fun2) = ReverseProgram.put(out2, None, None, Some((prog, fun))).head
    checkProg(out2, fun2, prog2)
  }

  test("Variable assigment keeps the shape") {
    val expected1 = "Hello world"
    val expected2 = "We are the children"

    val funDef = function(
      let(vText.toVal, "Hello world")(v => v)
    )(inoxTypeOf[String])
    val prog = mkProg(funDef)
    checkProg(expected1, funDef.id, prog)

    val (prog2, funId2) = repairProgram(funDef, prog, expected2)
    checkProg(expected2, funId2, prog2)

    // testing the shape.
    prog2 getBodyOf funId2 andMatch {
      case l@Let(vd, expr, body) =>
        if(!isVarIn(vd.id, body)) fail(s"There was no use of the variable $v in the given let-expression: $l")
    }
  }

  test("Change in output not modifying a variable but keeping the shape") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("pre", WebElement(TextNode("Hello world"))::Nil)

    val funDef = function(
      let(vText.toVal, StringLiteral("Hello world"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]())
      ))(inoxTypeOf[Element])
    val prog = mkProg(funDef)
    checkProg(expected1, funDef.id, prog)

    val (prog2, funId2) = repairProgram(funDef, prog, expected2)
    checkProg(expected2, funId2, prog2)

    // testing the shape.
    prog2 getBodyOf funId2 andMatch {
      case l@Let(vd, expr, body) =>
        if(!isVarIn(vd.id, body)) fail(s"There was no use of the variable $v in the given let-expression: $l")
    }
  }

  test("Variable assigment keeps the shape if deep embedded") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(TextNode("We are the children"))::Nil)

    val funDef = function(
      let(vText.toVal, StringLiteral("Hello world"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]())
      ))(inoxTypeOf[Element])
    val prog = mkProg(funDef)
    checkProg(expected1, funDef.id, prog)

    val (prog2, funId2) = repairProgram(funDef, prog, expected2)
    checkProg(expected2, funId2, prog2)

    // testing the shape.
    prog2 getBodyOf funId2 andMatch {
      case l@Let(vd, expr, body) =>
        if(!isVarIn(vd.id, body)) fail(s"There was no use of the variable $v in the given let-expression: $l")
    }
  }

  test("2 Variable assigments deep embedded") {
    val main = FreshIdentifier("main")
    val text = variable[String]("text")
    val attr = variable[WebAttribute]("attr")
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil, WebAttribute("class", "bgfont")::Nil)
    val expected2 = Element("div", WebElement(TextNode("We are the children"))::Nil, WebAttribute("class", "bgfontbig")::Nil)

    val funDef = function(
      let(text.toVal, "Hello world")(v =>
        let(attr.toVal, _WebAttribute("class", "bgfont"))(a =>
          _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](a), _List[WebStyle]())
        )
      ))(inoxTypeOf[Element])
    val prog = mkProg(funDef)
    checkProg(expected1, funDef.id, prog)

    val (prog2, funId2) = repairProgram(funDef, prog, expected2)
    checkProg(expected2, funId2, prog2)

    // testing the shape.
    prog2 getBodyOf funId2 andMatch {
      case l@Let(vd, expr, l2@Let(vd2, expr2, body)) =>
        if(!isVarIn(vd.id, body)) fail(s"There was no use of the variable $v in the given let-expression: $l")
        if(!isVarIn(vd2.id, body)) fail(s"There was no use of the variable $v in the given let-expression: $l")
    }
  }

  test("Variable assigment used twice") {
    val initial   = Element("div", WebElement(TextNode("red"))::Nil,  Nil, WebStyle("color", "red")::Nil)
    val out2      = Element("div", WebElement(TextNode("blue"))::Nil, Nil, WebStyle("color", "red")::Nil)
    val out2bis      = Element("div", WebElement(TextNode("red"))::Nil, Nil, WebStyle("color", "blue")::Nil)
    val expected2 = Element("div", WebElement(TextNode("blue"))::Nil, Nil, WebStyle("color", "blue")::Nil)

    val funDef = function(
      let(vText.toVal, StringLiteral("red"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle](_WebStyle("color", v)))
      ))(inoxTypeOf[Element])
    val prog = mkProg(funDef)
    checkProg[Element](initial, funDef.id, prog)

    val (prog2, funId2) = repairProgram(funDef, prog, out2)
    checkProg(expected2, funId2, prog2)

    val (prog3, funId3) = repairProgram(funDef, prog, out2bis)
    checkProg(expected2, funId3, prog3)

    val (prog4, funId4) = repairProgram(funDef, prog, out2)
    checkProg(expected2, funId4, prog4)
  }

  test("Variable assigment same, outer structure") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(Element("b", WebElement(TextNode("Hello world"))::Nil))::Nil)

    val funDef = function(
      let(vText.toVal, StringLiteral("Hello world"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]())
      ))(inoxTypeOf[Element])
    val prog = mkProg(funDef)
    checkProg[Element](expected1, funDef.id, prog)

    val (prog2, funId2) = repairProgram(funDef, prog, expected2)
    checkProg(expected2, funId2, prog2)

    // testing the shape.
    prog2 getBodyOf funId2 andMatch {
      case l@Let(vd, expr, body) =>
        if(!isVarIn(vd.id, body)) fail(s"There was no use of the variable $v in the given let-expression: $l")
    }
  }

  val lambda = Lambda(Seq(v.toVal),
    _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]()))

  for((funDef, msg) <- Seq(
    (function(Application(lambda, Seq("Hello world")))(inoxTypeOf[Element]),
      "change an applied lambda's argument"),
    (function(let(build.toVal, lambda)(b => Application(b, Seq("Hello world"))))(inoxTypeOf[Element]),
      "Change a variable lambda's argument")
  )) test(msg) {
      val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
      val expected2 = Element("div", WebElement(TextNode("We are the children"))::Nil)
      val prog = mkProg(funDef)
      checkProg(expected1, funDef.id, prog)
      val (prog2, funId2) = repairProgram(funDef, prog, expected2)
      checkProg[Element](expected2, funId2, prog2)
      // testing the shape.
      prog2 getBodyOf funId2 andMatch {
        case Let(_, _, Application(_, Seq(StringLiteral(s)))) if msg == "Change a variable lambda's argument"
          => s shouldEqual "We are the children"
        case Application(_, Seq(StringLiteral(s))) if msg == "change an applied lambda's argument"
          => s shouldEqual "We are the children"
      }
    }

  for((funDef, msg) <- Seq(
    (function(Application(lambda, Seq("Hello world")))(inoxTypeOf[Element]),
      "Change an applied lambda's shape by wrapping an element"),
    (function(let(build.toVal, lambda)(b => Application(b, Seq("Hello world"))))(inoxTypeOf[Element]),
      "Change a variable lambda's shape by wrapping an element")
  )) test(msg) {
      val expected1 = Element("div", WebElement(TextNode("Hello world")) :: Nil)
      val expected2 = Element("div", WebElement(Element("b", WebElement(TextNode("Hello world")) :: Nil)) :: Nil)
      val prog = mkProg(funDef)
      checkProg(expected1, funDef.id, prog)
      val (prog2, funId2) = repairProgram(funDef, prog, expected2)
      checkProg(expected2, funId2, prog2)
      // testing that the lambda changed but keeps the variable.
      prog2 getBodyOf funId2 andMatch {
        case Let(_, newLambda@Lambda(Seq(v2), body), Application(_, Seq(StringLiteral(_))))
          if msg == "Change a variable lambda's shape by wrapping an element"
        =>
          if (!isVarIn(v2.id, body)) fail(s"There was no variable $v2 in the given lambda: $newLambda")
        case Application(newLambda@Lambda(Seq(v2), body), _)
          if msg == "Change an applied lambda's shape by wrapping an element"
          =>
          if (!isVarIn(v2.id, body)) fail(s"There was no variable $v2 in the given lambda: $newLambda")
      }
    }

  val lambda2 = Lambda(Seq(v.toVal),
    _Element("div", _List[WebElement](_WebElement(_Element("b", _List[WebElement](_WebElement(_TextNode(v))),
      _List[WebAttribute](), _List[WebStyle]()))), _List[WebAttribute](), _List[WebStyle]()))

  for((funDef, msg) <- Seq(
    (function(Application(lambda2, Seq("Hello world")))(inoxTypeOf[Element]),
      "Change an applied lambda's shape by unwrapping an element"),
    (function(let(build.toVal, lambda2)(b => Application(b, Seq("Hello world"))))(inoxTypeOf[Element]),
      "Change a variable lambda's shape by unwrapping an element")
  )) test(msg) {
    val expected1 = Element("div", WebElement(Element("b", WebElement(TextNode("Hello world"))::Nil))::Nil)
    val expected2 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val prog = mkProg(funDef)
    checkProg(expected1, funDef.id, prog)
    val (prog2, funId2) = repairProgram(funDef, prog, expected2)
    checkProg(expected2, funId2, prog2)
    // testing that the lambda changed but keeps the variable.
    prog2 getBodyOf funId2 andMatch {
      case Let(_, newLambda@Lambda(Seq(v2), body), Application(_, Seq(StringLiteral(_))))
        if msg == "Change a variable lambda's shape by unwrapping an element"
      =>
        if(!isVarIn(v2.id, body)) fail(s"There was no variable $v in the given lambda: $newLambda")
      case Application(newLambda@Lambda(Seq(v2), body), _)
        if msg == "Change an applied lambda's shape by unwrapping an element"
      => {
        if(!isVarIn(v2.id, body)) fail(s"There was no variable $v in the given lambda: $newLambda")
      }
    }
  }

  for((funDef, msg) <- Seq(
    (function(Application(lambda, Seq("Hello world")))(inoxTypeOf[Element]),
      "Change an applied lambda's shape by inserting a constant element"),
    (function(let(build.toVal, lambda)(b => Application(b, Seq("Hello world"))))(inoxTypeOf[Element]),
      "Change a variable lambda's shape by inserting a constant element")
  ))  test(msg) {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(Element("br"))::WebElement(TextNode("Hello world"))::Nil)
    val (prog2, funId2) = repairProgram(funDef, mkProg(funDef), expected2)
    checkProg(expected2, funId2, prog2)

    // testing that the lambda changed but keeps the variable.
    prog2 getBodyOf funId2 andMatch {
      case Let(_, newLambda@Lambda(Seq(v2), body), Application(_, Seq(StringLiteral(_))))
        if msg == "Change a variable lambda's shape by inserting a constant element"
      =>
        if(!isVarIn(v2.id, body)) fail(s"There was no variable $v in the given lambda: $newLambda")
      case Application(newLambda@Lambda(Seq(v2), body), _)
        if msg == "Change an applied lambda's shape by inserting a constant element"
      =>
        if(!isVarIn(v2.id, body)) fail(s"There was no variable $v in the given lambda: $newLambda")
    }
  }

  test("Change a variable which went through a lambda") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(TextNode("We are the children"))::WebElement(TextNode("Hello world"))::Nil)
    val expected2bis = Element("div", WebElement(TextNode("Hello world"))::WebElement(TextNode("We are the children"))::Nil)
    val expected3 = Element("div", WebElement(TextNode("We are the children"))::WebElement(TextNode("We are the children"))::Nil)
    val lambda = Lambda(Seq(v.toVal),
      _Element("div", _List[WebElement](_WebElement(_TextNode(v)),_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]()))

    val funDef = function(
      let(build.toVal, lambda)(b =>
        Application(b, Seq("Hello world"))
      ))(inoxTypeOf[Element])

    val prog = mkProg(funDef)
    checkProg(expected1, funDef.id, prog)

    val (prog2, funId2) = repairProgram(funDef, prog, expected2)
    checkProg(expected3, funId2, prog2)

    val (prog3, funId3) = repairProgram(funDef, prog, expected2bis)
    checkProg(expected3, funId3, prog3)

    val (prog4, funId4) = repairProgram(funDef, prog, expected3)
    checkProg(expected3, funId4, prog4)
  }

  /* Add tests for:
     Closures
     List mapping, flatten, flatmap, filter.
     Multiple arguments changed in lambdas
     String concatenation
     Integers operations
     Migrate to constraint solving?

     XML transformation as in the paper.
    */
}
