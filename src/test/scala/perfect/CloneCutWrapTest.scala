package perfect
import inox._
import inox.trees._
import inox.trees.dsl._
import org.scalatest._
import matchers._
import Matchers.{=== => _, _}
import perfect.ReverseProgram.ProgramFormula

/**
  * Created by Mikael on 27/03/2017.
  */
class CloneCutWrapTest extends FunSuite with TestHelpers {
  import InoxConvertible._
  import XmlTrees._
  import StringConcatExtended._

  test("Formula assignment") {
    val va = variable[String]("a")
    val vb = variable[String]("b")
    val vc = variable[String]("c")
    val f = ReverseProgram.Formula(BooleanLiteral(true) && (vb +& "42") === vc && va === (vc +& vb) && vb === "17")
    f.assignments match {
      case None => fail(s"Could not extract assignments from $f")
      case Some(f) => f(va) shouldEqual Let(vb.toVal, "17", Let(vc.toVal, vb +& "42", Let(va.toVal, vc +& vb, va)))
    }
    val f2 = ReverseProgram.Formula(BooleanLiteral(true) && (vb +& "42") === va && va === (vc +& vb) && vb === "17")
    f2.assignments shouldEqual None
  }
  test("Wrap") {
    val output = _Node("i", children=_List[Node](_Node("Hello")))
    val pfun = function(
      let("ad" :: inoxTypeOf[String], "Hello"){ av =>
        _Node("i", children=_List[Node](_Node(av)))
      }
    )(inoxTypeOf[Node])
    pfun shouldProduce output

    val tree = valdef[Node](ProgramFormula.tree)
    val newOut = ProgramFormula(
      _Node("b", children=_List[Node](tree.toVariable)),
      tree.toVariable === _Node("i", children=_List[Node](_Node("Hello")))
    )
    pfun repairFrom newOut shouldProduce {
      _Node("b", children=_List[Node](_Node("i", children=_List[Node](_Node("Hello")))))
    } matchBody {
      case Let(ad, StringLiteral("Hello"), e) =>
        exprOps.variablesOf(e) should contain(ad.toVariable)
    }
  }

  test("Unwrap") {
    val output = _Node("b", children=_List[Node](_Node("i", children=_List[Node](_Node("Hello")))))
    val pfun = function(
      let("ad" :: inoxTypeOf[String], "Hello"){ av =>
        _Node("b", children=_List[Node](_Node("i", children=_List[Node](_Node(av)))))
      }
    )(inoxTypeOf[Node])
    pfun shouldProduce output

    val tree = valdef[Node](ProgramFormula.tree)
    val subtree = valdef[Node](ProgramFormula.subtree)
    val newOut = ProgramFormula(
      subtree.toVariable,
      tree.toVariable === _Node("b", children=_List[Node](subtree.toVariable)) &&
      subtree.toVariable === _Node("i", children=_List[Node](_Node("Hello")))
    )
    pfun repairFrom newOut shouldProduce {
      _Node("i", children=_List[Node](_Node("Hello")))
    } matchBody {
      case Let(ad, StringLiteral("Hello"), e) =>
        exprOps.variablesOf(e) should contain(ad.toVariable)
    }
  }

  test("String insert") {
    val output: Expr = "Hello"
    val pfun = function(
      let("a"::StringType, "Hello ")(av =>
        let("b"::StringType, " world")(bv =>
          av +& bv
        )
      )
    )(inoxTypeOf[String])

    val pfun2 = pfun repairFrom ProgramFormula.StringInsert("Hello", " big", "  world")
    pfun2 matchBody {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), va +& vb)) =>
        s shouldEqual "Hello big "
        t shouldEqual " world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
    val pfun3 = pfun repairFrom ProgramFormula.StringInsert("Hello  ", "big ", "world")
    pfun3 matchBody {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), va +& vb)) =>
        s shouldEqual "Hello "
        t shouldEqual " big world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
    val expectedOut4 = ProgramFormula.StringInsert("Hello ", "big", " world")
    val pfun4_l = repairProgramList(pfun, expectedOut4, 2).take(2).toList
    pfun4_l.map(_.getBody).map{
      case Let(a, StringLiteral("Hello big"), Let(b, StringLiteral(" world"), va +& vb)) =>
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
        1
      case Let(a, StringLiteral("Hello "), Let(b, StringLiteral("big world"), va +& vb)) =>
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
        2
    }.sum shouldEqual 3
  }

  test("Split / Clone and paste") {
    val output: Expr = "Hello big beautiful world"
    val pfun = function(
      let("a"::StringType, "Hello big ")(av =>
        let("b"::StringType, "beautiful world")(bv =>
          av +& bv
        )
      )
    )(inoxTypeOf[String])

    pfun shouldProduce output

    val tree = variable[String](ProgramFormula.tree)
    val subtree = variable[String](ProgramFormula.subtree)
    val newOut = ProgramFormula(
      tree +& "! It is really " +& subtree  +& ".",
      tree === "Hello " +& subtree +& " world" &&
      subtree === "big beautiful"
    )

    val pfun2 = pfun repairFrom newOut shouldProduce
      "Hello big beautiful world! It is really big beautiful."
    pfun2 repairFrom "Hello big and beautiful world! It is really big beautiful." shouldProduce
                     "Hello big and beautiful world! It is really big and beautiful."
  }

  test("Clone") {

  }

  test("Cut") {

  }
}
