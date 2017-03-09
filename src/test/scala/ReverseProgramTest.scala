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
import sun.swing.SwingUtilities2.RepaintListener

import scala.reflect.runtime.universe.TypeTag


object Make {
  def apply[A: Constrainable, B](in: Id[A] => (A ~~> B)): (A ~~> B) = in(Id[A]())
}

/** Mixin for tests repairing programs */
trait RepairProgramTest {
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


class ReverseProgramTest extends FunSuite with RepairProgramTest {
  import Constrainable._

  val build = Variable(FreshIdentifier("build"), FunctionType(Seq(inoxTypeOf[String]), inoxTypeOf[Element]), Set())
  val v = variable[String]("v")
  val vText = variable[String]("text")

  test("Create a program from scratch") {
    val out = Element("div", WebElement(TextNode("Hello world"))::Nil)
    checkProg(out, generateProgram(out))
  }

  test("Change a constant output to another") {
    val out  = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val out2 = Element("pre", WebElement(TextNode("Hello code"))::Nil)
    val (prog, fun) = ReverseProgram.put(out, None, None, None).head
    checkProg(out2, ReverseProgram.put(out2, None, None, Some((prog, fun))).head)
  }

  test("Variable assigment keeps the shape") {
    val expected1 = "Hello world"
    val expected2 = "We are the children"

    val funDef = function(
      let(vText.toVal, "Hello world")(v => v)
    )(inoxTypeOf[String])
    val (prog, funId) = checkProg(expected1, mkProg(funDef), funDef.id)
    val pfun2 = checkProg(expected2, repairProgram(funDef, prog, expected2))
    pfun2 matchBody {
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
    val (prog, funId)   = checkProg(expected1, mkProg(funDef), funDef.id)
    val pfun2 = checkProg(expected2, repairProgram(funDef, prog, expected2))
    pfun2 matchBody {
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
    val (prog, _) = checkProg(expected1, mkProg(funDef), funDef.id)
    val pfun2 = checkProg(expected2, repairProgram(funDef, prog, expected2))
    pfun2 matchBody {
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
    val (prog, funId)   = checkProg(expected1, mkProg(funDef), funDef.id)
    val pfun2 = checkProg(expected2, repairProgram(funDef, prog, expected2))
    pfun2 matchBody {
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
    val (prog, _) = checkProg[Element](initial, mkProg(funDef), funDef.id)
    checkProg(expected2, repairProgram(funDef, prog, out2))
    checkProg(expected2, repairProgram(funDef, prog, out2bis))
    checkProg(expected2, repairProgram(funDef, prog, out2))
  }

  test("Variable assigment same, outer structure") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(Element("b", WebElement(TextNode("Hello world"))::Nil))::Nil)

    val funDef = function(
      let(vText.toVal, StringLiteral("Hello world"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]())
      ))(inoxTypeOf[Element])
    val (prog, _) = checkProg[Element](expected1, mkProg(funDef), funDef.id)
    val pfun2 = checkProg(expected2, repairProgram(funDef, prog, expected2))
    pfun2 matchBody {
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
      val (prog, funId)   = checkProg(expected1, mkProg(funDef), funDef.id)
      val pfun2 = checkProg[Element](expected2, repairProgram(funDef, prog, expected2))
      pfun2 matchBody {
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
      val (prog, funId)   = checkProg(expected1, mkProg(funDef), funDef.id)
      val pfun2 = checkProg(expected2, repairProgram(funDef, prog, expected2))
      pfun2 matchBody {
        case Let(_, newLambda@Lambda(Seq(v2), body), Application(_, Seq(StringLiteral(_))))
          if msg == "Change a variable lambda's shape by wrapping an element"
        => if (!isVarIn(v2.id, body)) fail(s"There was no variable $v2 in the given lambda: $newLambda")
        case Application(newLambda@Lambda(Seq(v2), body), _)
          if msg == "Change an applied lambda's shape by wrapping an element"
        => if (!isVarIn(v2.id, body)) fail(s"There was no variable $v2 in the given lambda: $newLambda")
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
    val (prog, funId)   = checkProg(expected1, mkProg(funDef), funDef.id)
    val pfun2 = checkProg(expected2, repairProgram(funDef, prog, expected2))
    pfun2 matchBody {
      case Let(_, newLambda@Lambda(Seq(v2), body), Application(_, Seq(StringLiteral(_))))
        if msg == "Change a variable lambda's shape by unwrapping an element"
      => if(!isVarIn(v2.id, body)) fail(s"There was no variable $v in the given lambda: $newLambda")
      case Application(newLambda@Lambda(Seq(v2), body), _)
        if msg == "Change an applied lambda's shape by unwrapping an element"
      => if(!isVarIn(v2.id, body)) fail(s"There was no variable $v in the given lambda: $newLambda")
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
    val pfun2 = checkProg(expected2, repairProgram(funDef, mkProg(funDef), expected2))
    pfun2 matchBody {
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

    val (prog, funId)  = checkProg(expected1, mkProg(funDef), funDef.id)
    checkProg(expected3, repairProgram(funDef, prog, expected2))
    checkProg(expected3, repairProgram(funDef, prog, expected2bis))
    checkProg(expected3, repairProgram(funDef, prog, expected3))
  }

  test("Change a variable captured by a closure lambda") {
    val expected1 = Element("div", WebElement(TextNode("Closure parameter"))::WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(TextNode("Changed parameter"))::WebElement(TextNode("Hello world"))::Nil)

    val closureParameter = ValDef(FreshIdentifier("closure"), inoxTypeOf[String], Set())
    val lambda = Lambda(Seq(v.toVal),
      _Element("div", _List[WebElement](_WebElement(_TextNode(closureParameter.toVariable)),_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]()))

    val funDef = function(
      let(closureParameter, "Closure parameter")(cp =>
        Application(lambda, Seq("Hello world"))
      ))(inoxTypeOf[Element])

    val (prog, fundId)  = checkProg(expected1, mkProg(funDef), funDef.id)
    val pfun2 = checkProg(expected2, repairProgram(funDef, prog, expected2))
    pfun2 matchBody {
      case funBody@Let(_, StringLiteral(s), Application(newLambda@Lambda(Seq(v2), body), Seq(StringLiteral(_))))
      => //println(funBody)
        if(!isVarIn(v2.id, body)) fail(s"There was no variable $v in the given lambda: $newLambda")
        s shouldEqual "Changed parameter"
    }
  }
  test("Reverse simple string concatenation") {
    val expected1 = "Hello world"
    val expected2 = "Hello buddy"
    val expected3 = "Hello bigworld"
    val expected4 = "Hello    world"

    val funDef = function(StringConcat("Hello ", "world"))(inoxTypeOf[String])
    val (prog, funId)   = checkProg(expected1, mkProg(funDef), funDef.id)
    val pfun2 = checkProg(expected2, repairProgram(funDef, prog, expected2))
    val pfun3 = checkProg(expected3, repairProgram(funDef, prog, expected3))
    val pfun4 = checkProg(expected4, repairProgram(funDef, prog, expected4))

    pfun2 matchBody { case StringConcat(StringLiteral(s), StringLiteral(t)) =>
      s shouldEqual "Hello "
      t shouldEqual "buddy"
    }
    pfun3 matchBody { case StringConcat(StringLiteral(s), StringLiteral(t)) =>
      s shouldEqual "Hello "
      t shouldEqual "bigword"
    }
    pfun4 matchBody { case StringConcat(StringLiteral(s), StringLiteral(t)) =>
      s shouldEqual "Hello    "
      t shouldEqual "world"
    }
  }

  test("Reverse variable string concatenation") {
    val expected1 = "Hello world"
    val expected2 = "Hello buddy"

    val ap = ValDef(FreshIdentifier("a"), inoxTypeOf[String], Set())
    val bp = ValDef(FreshIdentifier("b"), inoxTypeOf[String], Set())

    val funDef = function(
      let(ap, "Hello ")(av =>
      let(bp, "world")(bv =>
        StringConcat(av, bv)
      )
      ))(inoxTypeOf[String])

    val (prog, funId)   = checkProg(expected1, mkProg(funDef), funDef.id)
    val pfun2 = checkProg(expected2, repairProgram(funDef, prog, expected2))
    pfun2 matchBody {
      case funBody@Let(Seq(v1: ValDef), StringLiteral(s), Let(Seq(v2: ValDef), StringLiteral(t), body@StringConcat(_, _)))
      =>
        if(!isVarIn(v1.id, body)) fail(s"There was no variable $v1 in the given final expression: $funBody")
        if(!isVarIn(v2.id, body)) fail(s"There was no variable $v2 in the given final expression: $funBody")
        s shouldEqual "Hello "
        t shouldEqual "buddy"
    }
  }

  /* Add tests for:
     String concatenation
     List mapping, flatten, flatmap, filter.
     Multiple arguments changed in lambdas
     Integers operations
     Migrate to constraint solving?

     XML transformation as in the paper.
    */
}
