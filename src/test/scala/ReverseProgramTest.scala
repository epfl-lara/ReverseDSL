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

    val pfun = function(
      let(vText.toVal, "Hello world")(v => v)
    )(inoxTypeOf[String])
    checkProg(expected1, pfun)
    val pfun2 = checkProg(expected2, repairProgram(pfun, expected2))
    pfun2 matchBody {
      case l@Let(vd, expr, body) =>
        if(!isVarIn(vd.id, body)) fail(s"There was no use of the variable $v in the given let-expression: $l")
    }
  }

  test("Change in output not modifying a variable but keeping the shape") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("pre", WebElement(TextNode("Hello world"))::Nil)

    val pfun = function(
      let(vText.toVal, StringLiteral("Hello world"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]())
      ))(inoxTypeOf[Element])
    checkProg(expected1, pfun)
    val pfun2 = checkProg(expected2, repairProgram(pfun, expected2))
    pfun2 matchBody {
      case l@Let(vd, expr, body) =>
        if(!isVarIn(vd.id, body)) fail(s"There was no use of the variable $v in the given let-expression: $l")
    }
  }

  test("Variable assigment keeps the shape if deep embedded") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(TextNode("We are the children"))::Nil)

    val pfun = function(
      let(vText.toVal, StringLiteral("Hello world"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]())
      ))(inoxTypeOf[Element])
    checkProg(expected1, pfun)
    val pfun2 = checkProg(expected2, repairProgram(pfun, expected2))
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

    val pfun = function(
      let(text.toVal, "Hello world")(v =>
        let(attr.toVal, _WebAttribute("class", "bgfont"))(a =>
          _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](a), _List[WebStyle]())
        )
      ))(inoxTypeOf[Element])
    checkProg(expected1, pfun)
    val pfun2 = checkProg(expected2, repairProgram(pfun, expected2))
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

    val pfun = function(
      let(vText.toVal, StringLiteral("red"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle](_WebStyle("color", v)))
      ))(inoxTypeOf[Element])
    checkProg(initial, pfun)
    checkProg(expected2, repairProgram(pfun, out2))
    checkProg(expected2, repairProgram(pfun, out2bis))
    checkProg(expected2, repairProgram(pfun, out2))
  }

  test("Variable assigment same, outer structure") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(Element("b", WebElement(TextNode("Hello world"))::Nil))::Nil)

    val pfun = function(
      let(vText.toVal, StringLiteral("Hello world"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]())
      ))(inoxTypeOf[Element])
    checkProg(expected1, pfun)
    val pfun2 = checkProg(expected2, repairProgram(pfun, expected2))
    pfun2 matchBody {
      case l@Let(vd, expr, body) =>
        if(!isVarIn(vd.id, body)) fail(s"There was no use of the variable $v in the given let-expression: $l")
    }
  }

  val lambda = Lambda(Seq(v.toVal),
    _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]()))

  for((pfun, msg) <- Seq(
    (function(Application(lambda, Seq("Hello world")))(inoxTypeOf[Element]),
      "change an applied lambda's argument"),
    (function(let(build.toVal, lambda)(b => Application(b, Seq("Hello world"))))(inoxTypeOf[Element]),
      "Change a variable lambda's argument")
  )) test(msg) {
      val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
      val expected2 = Element("div", WebElement(TextNode("We are the children"))::Nil)
      checkProg(expected1, pfun)
      val pfun2 = checkProg(expected2, repairProgram(pfun, expected2))
      pfun2 matchBody {
        case Let(_, _, Application(_, Seq(StringLiteral(s)))) if msg == "Change a variable lambda's argument"
          => s shouldEqual "We are the children"
        case Application(_, Seq(StringLiteral(s))) if msg == "change an applied lambda's argument"
          => s shouldEqual "We are the children"
      }
    }

  for((pfun, msg) <- Seq(
    (function(Application(lambda, Seq("Hello world")))(inoxTypeOf[Element]),
      "Change an applied lambda's shape by wrapping an element"),
    (function(let(build.toVal, lambda)(b => Application(b, Seq("Hello world"))))(inoxTypeOf[Element]),
      "Change a variable lambda's shape by wrapping an element")
  )) test(msg) {
      val expected1 = Element("div", WebElement(TextNode("Hello world")) :: Nil)
      val expected2 = Element("div", WebElement(Element("b", WebElement(TextNode("Hello world")) :: Nil)) :: Nil)
      checkProg(expected1, pfun)
      val pfun2 = checkProg(expected2, repairProgram(pfun, expected2))
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

  for((pfun, msg) <- Seq(
    (function(Application(lambda2, Seq("Hello world")))(inoxTypeOf[Element]),
      "Change an applied lambda's shape by unwrapping an element"),
    (function(let(build.toVal, lambda2)(b => Application(b, Seq("Hello world"))))(inoxTypeOf[Element]),
      "Change a variable lambda's shape by unwrapping an element")
  )) test(msg) {
    val expected1 = Element("div", WebElement(Element("b", WebElement(TextNode("Hello world"))::Nil))::Nil)
    val expected2 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    checkProg(expected1, pfun)
    val pfun2 = checkProg(expected2, repairProgram(pfun, expected2))
    pfun2 matchBody {
      case Let(_, newLambda@Lambda(Seq(v2), body), Application(_, Seq(StringLiteral(_))))
        if msg == "Change a variable lambda's shape by unwrapping an element"
      => if(!isVarIn(v2.id, body)) fail(s"There was no variable $v in the given lambda: $newLambda")
      case Application(newLambda@Lambda(Seq(v2), body), _)
        if msg == "Change an applied lambda's shape by unwrapping an element"
      => if(!isVarIn(v2.id, body)) fail(s"There was no variable $v in the given lambda: $newLambda")
    }
  }

  for((pfun, msg) <- Seq(
    (function(Application(lambda, Seq("Hello world")))(inoxTypeOf[Element]),
      "Change an applied lambda's shape by inserting a constant element"),
    (function(let(build.toVal, lambda)(b => Application(b, Seq("Hello world"))))(inoxTypeOf[Element]),
      "Change a variable lambda's shape by inserting a constant element")
  ))  test(msg) {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(Element("br"))::WebElement(TextNode("Hello world"))::Nil)
    val pfun2 = checkProg(expected2, repairProgram(pfun, expected2))
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

    val pfun = function(
      let(build.toVal, lambda)(b =>
        Application(b, Seq("Hello world"))
      ))(inoxTypeOf[Element])

    checkProg(expected1, pfun)
    checkProg(expected3, repairProgram(pfun, expected2))
    checkProg(expected3, repairProgram(pfun, expected2bis))
    checkProg(expected3, repairProgram(pfun, expected3))
  }

  test("Change a variable captured by a closure lambda") {
    val expected1 = Element("div", WebElement(TextNode("Closure parameter"))::WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(TextNode("Changed parameter"))::WebElement(TextNode("Hello world"))::Nil)

    val closureParameter = ValDef(FreshIdentifier("closure"), inoxTypeOf[String], Set())
    val lambda = Lambda(Seq(v.toVal),
      _Element("div", _List[WebElement](_WebElement(_TextNode(closureParameter.toVariable)),_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]()))

    val pfun = function(
      let(closureParameter, "Closure parameter")(cp =>
        Application(lambda, Seq("Hello world"))
      ))(inoxTypeOf[Element])

    checkProg(expected1, pfun)
    val pfun2 = checkProg(expected2, repairProgram(pfun, expected2))
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

    val pfun = function(StringConcat("Hello ", "world"))(inoxTypeOf[String])
    checkProg(expected1, pfun)
    val pfun2 = checkProg(expected2, repairProgram(pfun, expected2))
    val pfun3 = checkProg(expected3, repairProgram(pfun, expected3, 3))
    val pfun4 = checkProg(expected4, repairProgram(pfun, expected4, 3))

    pfun2 matchBody { case StringConcat(StringLiteral(s), StringLiteral(t)) =>
      s shouldEqual "Hello "
      t shouldEqual "buddy"
    }
    pfun3 matchBody { case StringConcat(StringLiteral(s), StringLiteral(t)) =>
      s shouldEqual "Hello "
      t shouldEqual "bigworld"
    }
    pfun4 matchBody { case StringConcat(StringLiteral(s), StringLiteral(t)) =>
      s shouldEqual "Hello    "
      t shouldEqual "world"
    }
  }

  test("Reverse 1 variable string concatenation") {
    val expected1 = "Hello world"
    val expected2 = "Hello buddy"

    val ap = ValDef(FreshIdentifier("a"), inoxTypeOf[String], Set())

    val pfun = function(
      let(ap, "Hello ")(av =>
        StringConcat(av, "world")
      ))(inoxTypeOf[String])

    checkProg(expected1, pfun)
    val pfun2 = checkProg(expected2, repairProgram(pfun, expected2))
    pfun2 matchBody {
      case funBody@Let(v1, StringLiteral(s), body@StringConcat(_, StringLiteral(t)))
      =>
        if(!isVarIn(v1.id, body)) fail(s"There was no variable $v1 in the given final expression: $funBody")
        s shouldEqual "Hello "
        t shouldEqual "buddy"
    }
  }

  test("Reverse 2 variables string concatenation") {
    val expected1 = "Hello world"
    val expected2 = "Hello buddy"

    val ap = ValDef(FreshIdentifier("a"), inoxTypeOf[String], Set())
    val bp = ValDef(FreshIdentifier("b"), inoxTypeOf[String], Set())

    val pfun = function(
      let(ap, "Hello ")(av =>
      let(bp, "world")(bv =>
        StringConcat(av, bv)
      )
      ))(inoxTypeOf[String])

    checkProg(expected1, pfun)
    val pfun2 = checkProg(expected2, repairProgram(pfun, expected2))
    pfun2 matchBody {
      case funBody@Let(v1, StringLiteral(s), Let(v2, StringLiteral(t), body@StringConcat(_, _)))
      =>
        if(!isVarIn(v1.id, body)) fail(s"There was no variable $v1 in the given final expression: $funBody")
        if(!isVarIn(v2.id, body)) fail(s"There was no variable $v2 in the given final expression: $funBody")
        s shouldEqual "Hello "
        t shouldEqual "buddy"
    }
  }

  test("Reverse 2 variables string concatenation, one used twice.") {
    val ap = ValDef(FreshIdentifier("a"), inoxTypeOf[String], Set())
    val bp = ValDef(FreshIdentifier("b"), inoxTypeOf[String], Set())

    val pfun = function(
      let(ap, "Mikael")(av =>
        let(bp, " ")(bv =>
          StringConcat(StringConcat(av, bv), av)
        )
      ))(inoxTypeOf[String])

    checkProg("Mikael Mikael", pfun)
    checkProg("Hi Hi",   repairProgram(pfun, "Mikael Hi", 2))
    checkProg("Hi Hi",   repairProgram(pfun, "Hi Mikael"))
    checkProg("Hi Hi",   repairProgram(pfun, "Mikael Hi"))
    checkProg("Mikael   Mikael", repairProgram(pfun, "Mikael   Mikael", 3))
  }

  test("Reverse filter") {
    val ap = ValDef(FreshIdentifier("a"), inoxTypeOf[Int], Set())
    val pfun = function(
      FunctionInvocation(Utils.filter,Seq(inoxTypeOf[Int]),
        Seq(
          _List[Int](0, 1, 2, 6, 5, 5, 8),
          Lambda(Seq(ap), Modulo(ap.toVariable, 2) === 0)
        )
      )
    )(inoxTypeOf[List[Int]])

    checkProg(_List[Int](0, 2, 6, 8), pfun)
    repairProgram(pfun, _List[Int](0, 2, 10, 6, 8)) matchBody {
      case FunctionInvocation(_, _, Seq(list, _)) =>
        list shouldEqual _List[Int](0, 1, 2, 10, 6, 5, 5, 8)
    }
  }

  /* Add tests for:
     Integers operations
     filter with propagating variables.
     List mapping, flatten, flatmap, filter and custom user-defined lenses.
     Multiple arguments changed in lambdas
     Merging programs to implement clone-and-paste.
     XML transformation as in the paper.

     How to be faster btw?
    */

  /*
    test("Clone-and-paste simple") {
      val ap = ValDef(FreshIdentifier("a"), inoxTypeOf[String], Set())

      val pfun = function("Hello world,")(inoxTypeOf[String])
      val clonedBody = let(ap, "world")(av =>
        StringConcat(StringConcat(StringConcat("Hello ", av), ","), av)
      )
      val pfun2 = repairProgram(pfun, clonedBody)
      pfun2 matchBody { case v => v shouldEqual clonedBody }
    }


    test("Clone-and-paste the left part with an existing variable") {
      val ap = ValDef(FreshIdentifier("a"), inoxTypeOf[String], Set())
      val bp = ValDef(FreshIdentifier("b"), inoxTypeOf[String], Set())

      val initBody = let(ap, "world")(av =>
        StringConcat("Hello ", av)
      )
      val clonedBody = let(bp, "Hello")(bv =>
        StringConcat(StringConcat(bv, " world"), bv)
      )
      val pfun = function(initBody)(inoxTypeOf[String])
      val pfun2 = repairProgram(pfun, clonedBody)
      checkProg("Hello worldHello", pfun2)
      val pfun3 = repairProgram(pfun2, "Hi worldHello")
      checkProg("Hi worldHi", pfun2)

      pfun3 matchBody {
        case funBody@Let(v1, StringLiteral(s), Let(v2, StringLiteral(t), body@StringConcat(_, _))) =>
          s shouldEqual "Hi"
          t shouldEqual "world"
      }
    }

    test("Clone-and-paste overlapping another variable") {
      val ap = ValDef(FreshIdentifier("a"), inoxTypeOf[String], Set())
      val bp = ValDef(FreshIdentifier("b"), inoxTypeOf[String], Set())

      val initBody = let(ap, "big world")(av =>
        StringConcat("Hello ", av)
      )
      val clonedBody = let(bp, "Hello big")(bv =>
        StringConcat(StringConcat(bv, " world"), bv)
      )
      val pfun = function(initBody)(inoxTypeOf[String])
      val pfun2 = repairProgram(pfun, clonedBody)
      checkProg("Hello big worldHello big", pfun2)
      val pfun3 = repairProgram(pfun2, "Hi big worldHello big")
      checkProg("Hi big worldHi big", pfun2)

      pfun3 matchBody {
        case funBody@Let(v1, StringLiteral(s), Let(v2, StringLiteral(t), body@StringConcat(_, _))) =>
          s shouldEqual "Hi big"
          t shouldEqual " world"
      }
    }*/

}
