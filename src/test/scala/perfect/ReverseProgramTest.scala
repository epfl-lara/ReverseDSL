package perfect
import legacy._
import perfect.InoxConvertible._List

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

class ReverseProgramTest extends FunSuite with TestHelpers {
  import InoxConvertible._
  import StringConcatExtended._
  import perfect.ProgramFormula
  import semanticlenses._

  val build = variable[String => Element]("build")
  val vText = variable[String]("text")

  implicit val symbols = Utils.defaultSymbols

  test("Create a program from scratch") {
    val out = Element("div", WebElement(TextNode("Hello world"))::Nil)
    checkProg(out, generateProgram(out))
  }

  test("Change a constant output to another") {
    val out  = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val out2 = Element("pre", WebElement(TextNode("Hello code"))::Nil)
    val pfun = ReverseProgram.put(None, out).head
    checkProg(out2, ReverseProgram.put(Some(pfun), out2).head)
  }

  test("Variable assigment keeps the shape") {
    val expected1 = "Hello world"
    val expected2 = "We are the children"
    val pfun = let(vText.toVal, "Hello world")(v => v)
    checkProg(expected1, pfun)
    val pfun2 = pfun repairFrom expected2 shouldProduce expected2
    pfun2 match {
      case l@Let(vd, expr, body) =>
        if (!isVarIn(vd.id, body)) fail(s"There was no use of the variable $vd in the given let-expression: $l")
    }
  }

  test("Change in output not modifying a variable but keeping the shape") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("pre", WebElement(TextNode("Hello world"))::Nil)

    val pfun = 
      let(vText.toVal, StringLiteral("Hello world"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]())
      )
    val pfun2 = pfun repairFrom expected2 shouldProduce expected2
    pfun2 match {
      case l@Let(vd, expr, body) =>
        if(!isVarIn(vd.id, body)) fail(s"There was no use of the variable $vd in the given let-expression: $l")
    }
  }

  test("Variable assigment keeps the shape if deep embedded") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(TextNode("We are the children"))::Nil)

    val pfun = 
      let(vText.toVal, StringLiteral("Hello world"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]())
      )
    checkProg(expected1, pfun)
    val pfun2 = pfun repairFrom expected2 shouldProduce expected2
    pfun2 match {
      case l@Let(vd, expr, body) =>
        if(!isVarIn(vd.id, body)) fail(s"There was no use of the variable $vd in the given let-expression: $l")
    }
  }

  test("2 Variable assigments deep embedded") {
    val main = FreshIdentifier("main")
    val text = variable[String]("text")
    val attr = variable[WebAttribute]("attr")
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil, WebAttribute("class", "bgfont")::Nil)
    val expected2 = Element("div", WebElement(TextNode("We are the children"))::Nil, WebAttribute("class", "bgfontbig")::Nil)

    val pfun = 
      let(text.toVal, "Hello world")(v =>
        let(attr.toVal, _WebAttribute("class", "bgfont"))(a =>
          _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](a), _List[WebStyle]())
        )
      )
    checkProg(expected1, pfun)
    val pfun2 = pfun repairFrom expected2 shouldProduce expected2
    pfun2 match {
      case l@Let(vd, expr, l2@Let(vd2, expr2, body)) =>
        if(!isVarIn(vd.id, body)) fail(s"There was no use of the variable $vd in the given let-expression: $l")
        if(!isVarIn(vd2.id, body)) fail(s"There was no use of the variable $vd in the given let-expression: $l")
    }
  }

  test("Variable assigment used twice") {
    val initial   = Element("div", WebElement(TextNode("red"))::Nil,  Nil, WebStyle("color", "red")::Nil)
    val out2      = Element("div", WebElement(TextNode("blue"))::Nil, Nil, WebStyle("color", "red")::Nil)
    val out2bis      = Element("div", WebElement(TextNode("red"))::Nil, Nil, WebStyle("color", "blue")::Nil)
    val expected2 = Element("div", WebElement(TextNode("blue"))::Nil, Nil, WebStyle("color", "blue")::Nil)

    val pfun = 
      let(vText.toVal, StringLiteral("red"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle](_WebStyle("color", v)))
      )
    checkProg(initial, pfun)
    pfun repairFrom out2 shouldProduce expected2
    pfun repairFrom out2bis shouldProduce expected2
    pfun repairFrom out2 shouldProduce expected2
  }

  test("Variable assigment same, outer structure") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(Element("b", WebElement(TextNode("Hello world"))::Nil))::Nil)

    val pfun = 
      let(vText.toVal, StringLiteral("Hello world"))(v =>
        _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]())
      )
    checkProg(expected1, pfun)
    val pfun2 = pfun repairFrom expected2 shouldProduce expected2
    pfun2 match {
      case l@Let(vd, expr, body) =>
        if(!isVarIn(vd.id, body)) fail(s"There was no use of the variable $vd in the given let-expression: $l")
    }
  }

  val lambda = \("v"::String)(v =>
    _Element("div", _List[WebElement](_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]()))

  def changeLambdasArgument(pfun: Expr, variable: Boolean) = {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(TextNode("We are the children"))::Nil)
    checkProg(expected1, pfun)
    val pfun2 = pfun repairFrom expected2 shouldProduce expected2
    pfun2 match {
      case Let(_, _, Application(_, Seq(StringLiteral(s)))) if variable
      => s shouldEqual "We are the children"
      case Application(_, Seq(StringLiteral(s))) if !variable
      => s shouldEqual "We are the children"
    }
  }

  test("change an applied lambda's argument") {
    changeLambdasArgument(Application(lambda, Seq("Hello world")), false)
  }
  test("Change a variable lambda's argument") {
    changeLambdasArgument(let(build.toVal, lambda)(b => Application(b, Seq("Hello world"))), true)
  }

  def changeLambdaShapeWrapping(pfun: Expr, variable: Boolean) = {
    val expected1 = Element("div", WebElement(TextNode("Hello world")) :: Nil)
    val expected2 = Element("div", WebElement(Element("b", WebElement(TextNode("Hello world")) :: Nil)) :: Nil)
    checkProg(expected1, pfun)
    val pfun2 = pfun repairFrom expected2 shouldProduce expected2
    pfun2 match {
      case Let(_, newLambda@Lambda(Seq(v2), body), Application(_, Seq(StringLiteral(_)))) if variable
      => if (!isVarIn(v2.id, body)) fail(s"There was no variable $v2 in the given lambda: $newLambda")
      case Application(newLambda@Lambda(Seq(v2), body), _) if !variable
      => if (!isVarIn(v2.id, body)) fail(s"There was no variable $v2 in the given lambda: $newLambda")
    }
  }
  test("Change an applied lambda's shape by wrapping an element") {
    changeLambdaShapeWrapping(Application(lambda, Seq("Hello world")), false)
  }
  test("Change a variable lambda's shape by wrapping an element") {
    changeLambdaShapeWrapping(let(build.toVal, lambda)(b => Application(b, Seq("Hello world"))), true)
  }

  val lambda2 = \("v"::String)(v =>
    _Element("div", _List[WebElement](_WebElement(_Element("b", _List[WebElement](_WebElement(_TextNode(v))),
      _List[WebAttribute](), _List[WebStyle]()))), _List[WebAttribute](), _List[WebStyle]()))

  def changeLambdaShapeUnwrapping(pfun: Expr, variable: Boolean) = {
    val expected1 = Element("div", WebElement(Element("b", WebElement(TextNode("Hello world"))::Nil))::Nil)
    val expected2 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    checkProg(expected1, pfun)
    val pfun2 = pfun repairFrom expected2 shouldProduce expected2
    pfun2 match {
      case Let(_, newLambda@Lambda(Seq(v2), body), Application(_, Seq(StringLiteral(_))))
        if variable
      => if(!isVarIn(v2.id, body)) fail(s"There was no variable $v2 in the given lambda: $newLambda")
      case Application(newLambda@Lambda(Seq(v2), body), _)
        if !variable
      => if(!isVarIn(v2.id, body)) fail(s"There was no variable $v2 in the given lambda: $newLambda")
    }
  }

  test("Change an applied lambda's shape by unwrapping an element") {
    Log activated changeLambdaShapeUnwrapping(Application(lambda2, Seq("Hello world")), false)
  }

  test("Change a variable lambda's shape by unwrapping an element") {
    changeLambdaShapeUnwrapping(let(build.toVal, lambda2)(b => Application(b, Seq("Hello world"))), true)
  }

  def changeLambdaShapeInsertingConstant(pfun: Expr, variable: Boolean) = {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(Element("br"))::WebElement(TextNode("Hello world"))::Nil)
    val pfun2 = pfun repairFrom expected2 shouldProduce expected2
    pfun2 match {
      case Let(_, newLambda@Lambda(Seq(v2), body), Application(_, Seq(StringLiteral(_)))) if variable
      =>
        if(!isVarIn(v2.id, body)) fail(s"There was no variable $v2 in the given lambda: $newLambda")
      case Application(newLambda@Lambda(Seq(v2), body), _) if !variable
      =>
        if(!isVarIn(v2.id, body)) fail(s"There was no variable $v2 in the given lambda: $newLambda")
    }
  }

  test("Change an applied lambda's shape by inserting a constant element") {
    changeLambdaShapeInsertingConstant(Application(lambda, Seq("Hello world")), false)
  }

  test("Change a variable lambda's shape by inserting a constant element") {
    changeLambdaShapeInsertingConstant(let(build.toVal, lambda)(b => Application(b, Seq("Hello world"))), true)
  }

  test("Change a variable which went through a lambda") {
    val expected1 = Element("div", WebElement(TextNode("Hello world"))::WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(TextNode("We are the children"))::WebElement(TextNode("Hello world"))::Nil)
    val expected2bis = Element("div", WebElement(TextNode("Hello world"))::WebElement(TextNode("We are the children"))::Nil)
    val expected3 = Element("div", WebElement(TextNode("We are the children"))::WebElement(TextNode("We are the children"))::Nil)
    val lambda = \("v"::String)(v =>
      _Element("div", _List[WebElement](_WebElement(_TextNode(v)),_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]()))

    val pfun = 
      let(build.toVal, lambda)(b =>
        Application(b, Seq("Hello world"))
      )

    checkProg(expected1, pfun)
    pfun repairFrom expected2 shouldProduce expected3
    pfun repairFrom expected2bis shouldProduce expected3
    pfun repairFrom expected3 shouldProduce expected3
  }

  test("Change a variable captured by a closure lambda") {
    val expected1 = Element("div", WebElement(TextNode("Closure parameter"))::WebElement(TextNode("Hello world"))::Nil)
    val expected2 = Element("div", WebElement(TextNode("Changed parameter"))::WebElement(TextNode("Hello world"))::Nil)

    val closureParameter = valdef[String]("closure")
    val lambda = \("v"::String)(v =>
      _Element("div", _List[WebElement](_WebElement(_TextNode(closureParameter.toVariable)),_WebElement(_TextNode(v))), _List[WebAttribute](), _List[WebStyle]()))

    val pfun = 
      let(closureParameter, "Closure parameter")(cp =>
        Application(lambda, Seq("Hello world"))
      )

    checkProg(expected1, pfun)
    val pfun2 = pfun repairFrom expected2 shouldProduce expected2
    pfun2 match {
      case funBody@Let(_, StringLiteral(s), Application(newLambda@Lambda(Seq(v2), body), Seq(StringLiteral(_))))
      => //Log(funBody)
        if(!isVarIn(v2.id, body)) fail(s"There was no variable $v2 in the given lambda: $newLambda")
        s shouldEqual "Changed parameter"
    }
  }
  test("Reverse simple string concatenation") {
    val expected1 = "Hello world"
    val expected2 = "Hello buddy"
    val expected3 = "Hello bigworld"
    val expected4 = "Hello    world"

    val pfun = "Hello " +& "world"
    checkProg(expected1, pfun)
    val pfun2 = pfun repairFrom expected2 shouldProduce expected2
    val pfun3 = checkProg(expected3, repairProgram(pfun, expected3, 3))
    val pfun4 = checkProg(expected4, repairProgram(pfun, expected4, 3))

    pfun2 match { case StringLiteral(s) +& StringLiteral(t) =>
      s shouldEqual "Hello "
      t shouldEqual "buddy"
    }
    pfun3 match { case StringLiteral(s) +& StringLiteral(t) =>
      s shouldEqual "Hello "
      t shouldEqual "bigworld"
    }
    pfun4 match { case StringLiteral(s) +& StringLiteral(t) =>
      (s, t) shouldEqual ("Hello    ", "world")
    }
  }

  test("Reverse 1 variable string concatenation") {
    val expected1 = "Hello world"
    val expected2 = "Hello buddy"

    val ap = valdef[String]("a")

    val pfun = 
      let(ap, "Hello ")(av =>
        av +& "world"
      )

    checkProg(expected1, pfun)
    val pfun2 = pfun repairFrom expected2 shouldProduce expected2
    pfun2 match {
      case funBody@Let(v1, StringLiteral(s), body@StringConcat(_, StringLiteral(t)))
      =>
        if(!isVarIn(v1.id, body)) fail(s"There was no variable $v1 in the given final expression: $funBody")
        s shouldEqual "Hello "
        t shouldEqual "buddy"
    }
  }

  test("Propose two possibles changes if we put a shared node in bold") {
    val m = valdef[InnerWebElement]("m")

    val normlOut = Element("div", List(
      WebElement(TextNode("Mikael")), WebElement(TextNode("Mikael"))))
    val givenOut = Element("div", List(
      WebElement(Element("b", WebElement(TextNode("Mikael"))::Nil)), WebElement(TextNode("Mikael"))))
    val possbOut = Element("div", List(
      WebElement(Element("b", WebElement(TextNode("Mikael"))::Nil)),
        WebElement(Element("b", WebElement(TextNode("Mikael"))::Nil))))

    val pfun = 
      let(m, _TextNode("Mikael"))( mv =>
        _Element("div", _List[WebElement](_WebElement(mv), _WebElement(mv)), _List[WebAttribute](), _List[WebStyle]())
      )
    println(givenOut: Expr)

    checkProg(normlOut, pfun)
    val s_pfun = repairProgramList(pfun, givenOut, 5)

    s_pfun.take(30).map(eval).toSet shouldEqual Set[Expr](givenOut, possbOut)
  }

  test("Reverse 2 variables string concatenation") {
    val expected1 = "Hello world"
    val expected2 = "Hello buddy"

    val ap = valdef[String]("a")
    val bp = valdef[String]("b")

    val pfun = 
      let(ap, "Hello ")(av =>
      let(bp, "world")(bv =>
        av +& bv
      )
      )

    checkProg(expected1, pfun)
    val pfun2 = pfun repairFrom expected2 shouldProduce expected2
    pfun2 match {
      case funBody@Let(v1, StringLiteral(s), Let(v2, StringLiteral(t), body@StringConcat(_, _)))
      =>
        if(!isVarIn(v1.id, body)) fail(s"There was no variable $v1 in the given final expression: $funBody")
        if(!isVarIn(v2.id, body)) fail(s"There was no variable $v2 in the given final expression: $funBody")
        s shouldEqual "Hello "
        t shouldEqual "buddy"
    }
  }

  test("Reverse 2 variables string concatenation, one used twice.") {
    val ap = valdef[String]("a")
    val bp = valdef[String]("b")

    val pfun = 
      let(ap, "Mikael")(av =>
        let(bp, " ")(bv =>
          av +& bv +& av
        )
      )

    /*checkProg("Hi Hi",   repairProgram(pfun, "Hi Hi"))
    checkProg("Mikael Mikael", pfun)
    checkProg("Hi Hi",   repairProgram(pfun, "Mikael Hi", 2))
    checkProg("Hi Hi",   repairProgram(pfun, "Hi Mikael", 2))*/
    checkProg("Mikael   Mikael", repairProgram(pfun, "Mikael   Mikael", 4)) match {
      case Let(_, StringLiteral(s), Let(_, StringLiteral(t), _)) =>
        s shouldEqual "Mikael"
        t shouldEqual "   "
    }
  }

  test("Propose the change between changing a variable and adding a new string") {
    val ap = valdef[String]("a")

    val pfun = 
      let(ap, "Mikael")(av =>
          av +& " is nice, " +& av
      )
    //checkProg("Mikael is nice, Mikael", pfun)
    val s_pfun2 = repairProgramList(pfun, "Mikael is nice, Mikael is clever", 3)
    //checkProg("Mikael is clever is nice, Mikael is clever", s_pfun2.head)
    checkProg("Mikael is nice, Mikael is clever", s_pfun2.tail.head) match {
      case Let(p, StringLiteral(s), _) =>
        s shouldEqual "Mikael"
    }
  }



  test("Reverse curried string arguments") {
    val pfun = 
      Application(
        Application(
        \("a"::String)(av =>
          \("b"::String)(bv =>
            av +& ":" +& bv
          )
        ), Seq("Winner")), Seq("Mikael"))
    
    checkProg("Winner:Mikael", pfun)
    checkProg("Winner:Viktor",   repairProgram(pfun, "Winner:Viktor")) match {
      case Application(Application(_, Seq(StringLiteral(s))), Seq(StringLiteral(t))) =>
        s shouldEqual "Winner"
        t shouldEqual "Viktor"
    }
  }


  test("Reverse filter") {
    val pfun = 
      E(Utils.filter)(Int)(
        _List[Int](0, 1, 2, 6, 5, 5, 8),
        \("a"::Int)( av =>  Modulo(av, 2) === 0)
      )

    checkProg(_List[Int](0, 2, 6, 8), pfun)
    repairProgram(pfun, _List[Int](0, 2, 10, 6, 8)) match {
      case FunctionInvocation(_, _, Seq(list, _)) =>
        list shouldEqual _List[Int](0, 1, 2, 10, 6, 5, 5, 8)
    }
  }

  test("Reverse filter with variable arguments") {
    val input = valdef[List[Int]]("input")
    val f = valdef[Int => Boolean]("f")
    val pfun = 
      let(input, _List[Int](0, 1, 2, 6, 5, 5, 8))(inputv =>
      let(f, \("a"::Int)(av => Modulo(av, 2) === 0))(fv =>
        E(Utils.filter)(Int)(inputv, fv)
      ))

    checkProg(_List[Int](0, 2, 6, 8), pfun)
    repairProgram(pfun, _List[Int](0, 2, 10, 6, 8)) match {
      case Let(input2, input2expr, Let(f2, f2expr, FunctionInvocation(_, _, Seq(arg1, arg2)))) =>
        arg1 shouldEqual input2.toVariable
        arg2 shouldEqual f2.toVariable
        input2expr shouldEqual _List[Int](0, 1, 2, 10, 6, 5, 5, 8)
    }
  }

  object Map {
    def apply(l: List[String], v: Variable => Expr) =
      E(Utils.map)(String, String)(
        l: Expr, \("ap"::String)(av => v(av))
      )

    def unapply(e: Expr) = e match {
      case FunctionInvocation(Utils.map, Seq(_, _),
      Seq(l, Lambda(Seq(vd), body))) => Some((l, vd.toVariable, body))
      case _ => None
    }
  }
  test("Reverse map") {
    val ap = valdef[String]("a")
    Map(List("A","B","D","E"), av => "- " +& av) repairFrom
      ListInsert(StringType, List("- A", "- B"), List("- C"), List("- D", "- E")) shouldProduce
      _List[String]("- A", "- B", "- C", "- D", "- E")

    val pfStr4 = StringInsert("- ", "B", "", AssociativeInsert.InsertAutomatic)
    Map(List("A","","C"), av => "- " +& av) repairFrom
    ProgramFormula(ListLiteral.concat(List("- A"), ListLiteral(List(pfStr4.expr), StringType), List("- C")), pfStr4.formula) shouldProduce
    _List[String]("- A", "- B", "- C")

    val pfun = Map(List("Margharita", "Salami", "Royal"), av => "Pizza " +& av)
    pfun shouldProduce
    _List[String]("Pizza Margharita", "Pizza Salami", "Pizza Royal") repairFrom
    _List[String]("Pizza Margharita", "Pizza Salami", "Pizza Sushi", "Pizza Royal") match {
      case Map(list, v, body) =>
        list shouldEqual _List[String]("Margharita", "Salami", "Sushi", "Royal")
    }

    val pfStr2 = StringInsert("", "*", " C", AssociativeInsert.InsertAutomatic)
    Map(List("A","B","C","D"), av => "- " +& av) repairFrom
    ProgramFormula(ListLiteral.concat(List("- A", "- B"), ListLiteral(List(pfStr2.expr), StringType), List("- D")), pfStr2.formula) shouldProduce
    _List[String]("* A", "* B", "* C", "* D")



    val pfStr3 = StringInsert("- B", "o", "", AssociativeInsert.InsertAutomatic)
    Map(List("A","B","C","D"), av => "- " +& av) repairFrom
    ProgramFormula(ListLiteral.concat(List("- A"), ListLiteral(List(pfStr3.expr), StringType), List("- C", "- D")), pfStr3.formula) shouldProduce
    _List[String]("- A", "- Bo", "- C", "- D")

    val pfStr3b = StringInsert("- ", "o", "B", AssociativeInsert.InsertAutomatic)
    Map(List("A","B","C","D"), av => "- " +& av) repairFrom
      ProgramFormula(ListLiteral.concat(List("- A"), ListLiteral(List(pfStr3b.expr), StringType), List("- C", "- D")), pfStr3b.formula) shouldProduce
      _List[String]("- A", "- oB", "- C", "- D")


    val pfStr = StringInsert("- ", "E", "", AssociativeInsert.InsertAutomatic)
    Map(List("A","B","C","D"), av => "- " +& av) repairFrom
      (ListInsert(StringType, List("- A", "- B"), List(), List(pfStr.expr)) combineWith pfStr.formula) shouldProduce
    _List[String]("- A", "- B", "- E")

    Map(List("A","B","D","E"), av => "- " +& av) repairFrom
    ListInsert(StringType, List("- A", "- B"), List(""), List("- D", "- E")) shouldProduce
    _List[String]("- A", "- B", "- ", "- D", "- E")


    Map(List("A","B","C","D"), av => "- " +& av) repairFrom
    ListInsert(StringType, List("- A", "- B", "- C", "- D"), List(""), List()) shouldProduce
    _List[String]("- A", "- B", "- C", "- D", "- ")

    Map(List("A","B","C","D"), av => "- " +& av) repairFrom
    ListInsert(StringType, List(), List(""), List("- A", "- B", "- C", "- D")) shouldProduce
    _List[String]("- ", "- A", "- B", "- C", "- D")

    pfun repairFrom _List[String]("The pizza Margharita", "Pizza Salami","Pizza Royal") shouldProduce
      _List[String]("The pizza Margharita", "The pizza Salami", "The pizza Royal") match {
      case Map(list, vd, prefix +& _) =>
        list shouldEqual _List[String]("Margharita", "Salami", "Royal")
        prefix shouldEqual StringLiteral("The pizza ")
    }
  }

  test("Reverse map where function comes from outside") {
    val program = let("p"::String, " !")(p =>
    let("f"::inoxTypeOf[String => String], \("x"::String)(x => x +& p))(f =>
      E(Utils.map)(String, String)(_List[String]("a", "b"), f)
    ))
    program shouldProduce _List[String]("a !", "b !")

    program repairFrom _List[String]("a ?", "b !") shouldProduce _List[String]("a ?", "b ?") match {
      case Let(pvd, StringLiteral(str),
      Let(fvd, Lambda(Seq(xvd), StringConcat(xv, pv)),
        FunctionInvocation(Utils.map, Seq(StringType, StringType), Seq(ListLiteral(List(StringLiteral("a"), StringLiteral("b")), _), fv))
      )) =>
        pvd.toVariable shouldEqual pv
        fvd.toVariable shouldEqual fv
        str shouldEqual " ?"
    }
  }

  test("Reverse flatmap") {
    val pfun = 
      E(Utils.flatmap)(String, String)(
          _List[String]("Margharita", "Royal", "Salami"),
          \("a"::String)(av => if_(av === StringLiteral("Royal")) {
            _List[String](av)
          } else_ {
            _List[String](av, av +& " with mushrooms")
          })
      )

    checkProg(_List[String]("Margharita", "Margharita with mushrooms", "Royal", "Salami", "Salami with mushrooms"), pfun)
    repairProgram(pfun, _List[String]("Margharita", "Margharita with champignons", "Royal", "Salami", "Salami with mushrooms")) shouldProduce
      _List[String]("Margharita", "Margharita with champignons", "Royal", "Salami", "Salami with champignons")
    repairProgram(pfun, _List[String]("Margharita", "Sushi with mushrooms", "Royal", "Salami", "Salami with mushrooms")) shouldProduce
      _List[String]("Sushi",      "Sushi with mushrooms", "Royal", "Salami", "Salami with mushrooms")
    repairProgram(pfun, _List[String]("Margharita", "Margharita with mushrooms", "Royalty", "Salami", "Salami with mushrooms")) shouldProduce
                        _List[String]("Margharita", "Margharita with mushrooms", "Royalty", "Royalty with mushrooms", "Salami", "Salami with mushrooms")

    repairProgram(pfun, _List[String]("Margharita", "Margharita with mushrooms", "Royal", "Jambon", "Jambon with mushrooms", "Salami", "Salami with mushrooms")) shouldProduce
      _List[String]("Margharita", "Margharita with mushrooms", "Royal", "Jambon", "Jambon with mushrooms", "Salami", "Salami with mushrooms") match {
      case FunctionInvocation(_, _, Seq(arg, lambda)) =>
        arg shouldEqual _List[String]("Margharita", "Royal", "Jambon", "Salami")
    }
  }

  test("Reverse mkString") {
    val ap = valdef[String]("a")
    object MkString {
      def apply(input: Expr, middle: Expr) = 
        FunctionInvocation(Utils.mkString,Seq(),
          Seq(
            input,
            middle
          )
        )
      def unapply(e: Expr): Option[(Expr, Expr)] = e match {
        case FunctionInvocation(Utils.mkString,Seq(),
      Seq(input, middle)
      ) => Some((input, middle))
        case _ => None
      }
    }

    MkString(List[String]("c"), "") repairFrom StringInsert("","kp", "c", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("")) => l shouldEqual _List[String]("kpc") }

    MkString(List[String]("a","c"), "") repairFrom StringInsert("a","b", "c", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("b")) => l shouldEqual _List[String]("a","c") }

    MkString(List[String]("a","b","c"), "\n") repairFrom StringInsert("a\n","d\n", "b\nc", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("\n")) => l shouldEqual _List[String]("a","d", "b", "c") }

    MkString(List[String]("a","dc"), "") repairFrom StringInsert("a","b", "c", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("")) => l shouldEqual _List[String]("a","bc") }

    MkString(List[String]("dc"), "") repairFrom StringInsert("","kp", "c", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("")) => l shouldEqual _List[String]("kpc") }

    /* MkString(List[String]("abc","def","gh"), "") repairFrom StringInsert("ab","#","efgh", AssociativeInsert.InsertAutomatic) match {
       case MkString(l, StringLiteral("#")) => l shouldEqual _List[String]("ab","ef","gh") }*/

    MkString(List[String]("c","ob","d"), "?#") repairFrom StringInsert("c?#o","m?#k", "d", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("?#")) => l shouldEqual _List[String]("c","om","kd") }

    MkString(List[String]("c","ob","d"), "?#") repairFrom StringInsert("c?#o","k", "d", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("?#")) => l shouldEqual _List[String]("c","okd") }

    MkString(List[String]("c","ob","d"), "?#") repairFrom StringInsert("c?#o","k?#", "d", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("?#")) => l shouldEqual _List[String]("c","ok", "d") }

    MkString(List[String]("c","d"), "?#") repairFrom StringInsert("c?",":", "#d", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("?:#")) => l shouldEqual _List[String]("c","d") }

    MkString(List[String]("c","d","e"), "#") repairFrom StringInsert("","m#k", "#e", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("#")) => l shouldEqual _List[String]("m","k","e") }

    MkString(List[String]("c","d","e"), "#") repairFrom StringInsert("c#","m#k", "#e", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("#")) => l shouldEqual _List[String]("c","m","k","e") }

    MkString(List[String]("c","d","e"), "#") repairFrom StringInsert("c","m#k", "e", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("#")) => l shouldEqual _List[String]("cm","ke") }

    MkString(List[String]("c","d","e"), "#") repairFrom StringInsert("c","m#k#", "e", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("#")) => l shouldEqual _List[String]("cm","k","e") }

    MkString(List[String]("c","d","e"), "#") repairFrom StringInsert("c","#m#k", "e", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("#")) => l shouldEqual _List[String]("c","m","ke") }

    MkString(List[String]("c","d","e"), "#") repairFrom StringInsert("c","#m#k#", "e", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("#")) => l shouldEqual _List[String]("c","m","k","e") }

    MkString(List[String]("c"), "#") repairFrom StringInsert("c","k#d", "", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("#")) => l shouldEqual _List[String]("ck","d") }

    MkString(List[String]("a","c", "d"), "#") repairFrom StringInsert("a","b", "d", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("#")) => l shouldEqual _List[String]("abd") }

    MkString(List[String]("a", "b", "c"), "#") repairFrom StringInsert("a#","e#f#q","b#c", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("#")) => l shouldEqual _List[String]("a", "e", "f", "qb", "c") }

    MkString(List[String](), "#") repairFrom StringInsert("","a#b","", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("#")) => l shouldEqual _List[String]("a","b") }

    MkString(List[String](""), "") repairFrom StringInsert("","aloha", "", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("")) => l shouldEqual _List[String]("aloha") }


    val pfun = MkString(List("- Margharita", "- Royal", "- Salami"), "\n")

    pfun shouldProduce "- Margharita\n- Royal\n- Salami"




    MkString(List[String](), "") repairFrom StringInsert("","aloha", "", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("")) =>
        l shouldEqual _List[String]("aloha")
    }

    pfun repairFrom StringInsert("- Margharita\n- Royal\n", "\n", "- Salami", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("\n")) =>
        l shouldEqual _List[String]("- Margharita", "- Royal", "", "- Salami")
    }
    pfun repairFrom "- Margharita\n- Royal\n- Ham\n- Salami" match {
      case MkString(l, StringLiteral("\n")) =>
        l shouldEqual _List[String]("- Margharita", "- Royal", "- Ham", "- Salami")
    }
    pfun repairFrom "- Margharita\n- Salami" match {
      case MkString(l, StringLiteral("\n")) =>
        l shouldEqual  _List[String]("- Margharita", "- Salami")
    }
    pfun repairFrom StringInsert("- Margharita", ",", "- Royal\n- Salami", AssociativeInsert.InsertAutomatic) shouldProduce "- Margharita,- Royal,- Salami"
    pfun repairFrom StringInsert("", "  ","- Margharita\n- Royal\n- Salami", AssociativeInsert.InsertAutomatic) shouldProduce "  - Margharita\n- Royal\n- Salami"
    pfun repairFrom StringInsert("- Margharita","s","\n- Royal\n- Salami", AssociativeInsert.InsertAutomatic) shouldProduce "- Margharitas\n- Royal\n- Salami"
    pfun repairFrom StringInsert("- Margharita\n","  ","- Royal\n- Salami", AssociativeInsert.InsertAutomatic) shouldProduce "- Margharita\n  - Royal\n- Salami"
    pfun repairFrom StringInsert("- Margharita\n- Royal","s","\n- Salami", AssociativeInsert.InsertAutomatic) shouldProduce "- Margharita\n- Royals\n- Salami"
    pfun repairFrom StringInsert("- Margharita\n- Royal\n","  ","- Salami", AssociativeInsert.InsertAutomatic) shouldProduce "- Margharita\n- Royal\n  - Salami"
    pfun repairFrom StringInsert("- Margharita\n- Royal\n- Salami","s", "", AssociativeInsert.InsertAutomatic) shouldProduce "- Margharita\n- Royal\n- Salamis"
    pfun repairFrom StringInsert("- Margharita","\n","\n- Royal\n- Salami", AssociativeInsert.InsertAutomatic) shouldProduce "- Margharita\n\n- Royal\n- Salami"
    pfun repairFrom StringInsert("- Margharita\n","\n","- Royal\n- Salami", AssociativeInsert.InsertAutomatic) shouldProduce "- Margharita\n\n- Royal\n- Salami"
    pfun repairFrom StringInsert("- Margharita\n","- Sushi\n","- Royal\n- Salami", AssociativeInsert.InsertAutomatic) shouldProduce "- Margharita\n- Sushi\n- Royal\n- Salami"

    pfun repairFrom StringInsert("- ","Ham","\n- Royal\n- Salami", AssociativeInsert.InsertAutomatic) match {
      case MkString(l, StringLiteral("\n")) =>
        l shouldEqual _List[String]("- Ham", "- Royal", "- Salami")
    }
  }

  test("Reverse list concatenation") {
    val pfun = 
      E(Utils.listconcat)(String)(
        _List[String]("Margharita", "Salami"),
        _List[String]("Sudjuk")
      )

    checkProg(_List[String]("Margharita", "Salami", "Sudjuk"), pfun)
    val s_pfun2 = Log activated repairProgramList(pfun, _List[String]("Margharita", "Salami", "Salmon", "Sudjuk"), 2).take(2)
    s_pfun2.map{ pfun2 =>
      pfun2 match {
        case FunctionInvocation(_, _, Seq(a, b)) =>
          (a, b)
      }
    }.toSet shouldEqual Set[(Expr, Expr)](
      (_List[String]("Margharita", "Salami", "Salmon"), _List[String]("Sudjuk")),
      (_List[String]("Margharita", "Salami"), _List[String]("Salmon", "Sudjuk"))
    )

    repairProgram(pfun, _List[String]("Margharita", "Salmon", "Salami", "Sudjuk")) match {
      case FunctionInvocation(_, _, Seq(a, b)) =>
        a shouldEqual _List[String]("Margharita", "Salmon", "Salami")
        b shouldEqual _List[String]("Sudjuk")
    }

    repairProgram(pfun, _List[String]("Margharita", "Salami", "Sudjuk", "Salmon")) match {
      case FunctionInvocation(_, _, Seq(a, b)) =>
        a shouldEqual _List[String]("Margharita", "Salami")
        b shouldEqual _List[String]("Sudjuk", "Salmon")
    }
  }

  test("Tuple select repair") {
    import ImplicitTuples._
    val pfun =
      _Tuple2(String, String)("Hello", "world").getField(_1)

    checkProg("Hello", pfun)
    checkProg("Dear", repairProgram(pfun, "Dear")) match {
      case ADTSelector(ADT(_, Seq(StringLiteral(s), StringLiteral(t))), `_1`) =>
        s shouldEqual "Dear"
        t shouldEqual "world"
    }
  }

  test("Tuple select repair preserving input programs") {
    import ImplicitTuples._
    val pfun = 
      _Tuple2(String, String)("Hello" +& ", ", "world").getField(_1)

    checkProg("Hello, ", pfun)
    checkProg("Hello! ", repairProgram(pfun, "Hello! ")) match {
      case ADTSelector(ADT(_,
        Seq(StringLiteral(s) +& StringLiteral(t), StringLiteral(w))), `_1`) =>
        s shouldEqual "Hello"
        t shouldEqual "! "
        w shouldEqual "world"
    }
  }

  test("Tuple select repair when used twice.") {
    import ImplicitTuples._
    val tp = T(tuple2)(StringType, StringType)
    val a = ValDef(FreshIdentifier("a"), tp)
    val pfun = 
      let(a, _Tuple2(String, String)("Mikael", " "))(av =>
        //StringConcat(StringConcat(ADTSelector(av, _1), ADTSelector(av, _2)), ADTSelector(av, _1))
        (ADTSelector(av, _1) +& ADTSelector(av, _2)) +& ADTSelector(av, _1)
      )

    checkProg("Mikael Mikael", pfun)
    checkProg("Mar Mar", repairProgram(pfun, "Mar Mar"))
    checkProg("Mar Mar", repairProgram(pfun, "Mikael Mar"))
    checkProg("Mar Mar", repairProgram(pfun, "Mar Mikael"))
  }

  test("Tuple conflict") {
    import ImplicitTuples._
    val tp = T(tuple2)(StringType, StringType)
    val a = ValDef(FreshIdentifier("a"), tp)
    val pfun = 
      let("a":: StringType, "Hello")(av =>
        ADT(tp, Seq(av, av))
      )

    checkProg(("Hello", "Hello"), pfun)
    checkProg(("World", "World"), repairProgram(pfun, ("Hello", "World")))
    checkProg(("World", "World"), repairProgram(pfun, ("World", "Hello")))
    /*repairProgramList(pfun, ("Hey", "Jude"), 2).take(2).map(eval).toSet shouldEqual
    Set[Expr](("Hey", "Hey"), ("Jude", "Jude"))*/
    // Double repair !
  }

  test("If-then-else") {
    val pfun = 
      let("a" :: StringType, "Hello")(av =>
        if_(av === "Hello") { av } else_ { av +& " !" }
      )
    checkProg("Hello", pfun)
    checkProg("Mikael !", repairProgram(pfun, "Mikael"))
  }

  /* Add tests for:
     Integers operations
     List flatten, flatmap,
     Bag, Set
     User-defined lenses.
     Merging programs to implement clone-and-paste.
     XML transformation as in the paper.

     How to be faster btw?
    */

}
