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
    val pfun = function(
      let("a"::StringType, "Hello ")(av =>
        let("b"::StringType, " world")(bv =>
          av +& bv
        )
      )
    )(inoxTypeOf[String])

    pfun repairFrom ProgramFormula.StringInsert("Hello", " big", "  world") matchBody {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), va +& vb)) =>
        s shouldEqual "Hello big "
        t shouldEqual " world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
    pfun repairFrom ProgramFormula.StringInsert("Hello  ", "big ", "world") matchBody {
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

  test("Nested string insert") {
    val pfun = function(
      let("a"::StringType, "Hello ")(av =>
        let("b"::StringType, "big ")(bv =>
          let("c"::StringType, "world")(cv =>
            av +& bv +& cv
          )
        )
      )
    )(inoxTypeOf[String])

    pfun repairFrom ProgramFormula.StringInsert("Hello big", " big", " world") matchBody {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), Let(c, StringLiteral(u), va +& vb +& vc))) =>
        s shouldEqual "Hello "
        t shouldEqual "big big "
        u shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
        vc shouldEqual c.toVariable
    }
    pfun repairFrom ProgramFormula.StringInsert("Hello"," big"," big world") matchBody {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), Let(c, StringLiteral(u), va +& vb +& vc))) =>
        s shouldEqual "Hello big "
        t shouldEqual "big "
        u shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
        vc shouldEqual c.toVariable
    }
  }

  test("Nested string insert direct") {
    val pfun = function(
      "Hello " +& "big " +& "world"
    )(inoxTypeOf[String])

    pfun repairFrom ProgramFormula.StringInsert("Hello big", " big", " world") matchBody {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual "big big "
        u shouldEqual "world"
    }
    pfun repairFrom ProgramFormula.StringInsert("Hello"," big"," big world") matchBody {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello big "
        t shouldEqual "big "
        u shouldEqual "world"
    }
  }

  test("String insert direct test space weight") {
    val pfun = function(
      "Hello " +& "world"
    )(inoxTypeOf[String])

    pfun repairFrom ProgramFormula.StringInsert("Hello ", " ", "world") matchBody {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello  "
        t shouldEqual "world"
    }
    pfun repairFrom ProgramFormula.StringInsert("Hello ", "big", "world") matchBody {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello "
        t shouldEqual "bigworld"
    }

    val pfun2 = function(
      "Hello" +& " world"
    )(inoxTypeOf[String])

    pfun2 repairFrom ProgramFormula.StringInsert("Hello", " ", " world") matchBody {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello"
        t shouldEqual "  world"
    }
    pfun2 repairFrom ProgramFormula.StringInsert("Hello", "big", " world") matchBody {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hellobig"
        t shouldEqual " world"
    }
  }

  test("Nested string modification direct") {
    val pfun = function(
      "Hello " +& "big " +& "world"
    )(inoxTypeOf[String])

    pfun repairFrom ProgramFormula.StringInsert("Hello big ","change","") matchBody {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual "big "
        u shouldEqual "change"
    }

    pfun repairFrom ProgramFormula.StringInsert("","Good afternoon ","big world") matchBody {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Good afternoon "
        t shouldEqual "big "
        u shouldEqual "world"
    }

    pfun repairFrom ProgramFormula.StringInsert("Hello ","great"," world") matchBody {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual "great "
        u shouldEqual "world"
    }

    repairProgramList(pfun, ProgramFormula.StringInsert("Hello", ", amazing", " world"), 2).take(2).toList.map(x => x.getBody match {
      case StringLiteral("Hello, amazing") +& StringLiteral(" ") +& StringLiteral("world") =>
        1
      case StringLiteral("Hello") +& StringLiteral(", amazing ") +& StringLiteral("world") =>
        2
    }).sum shouldEqual 3

  }

  test("String delete") {
    val pfun = function(
      let("a"::StringType, "Hello big ")(av =>
        let("b"::StringType, " big world")(bv =>
          av +& bv
        )
      )
    )(inoxTypeOf[String])
    // "Hello big  big world"
    pfun repairFrom ProgramFormula.StringInsert("Hello",""," big world") matchBody {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), va +& vb)) =>
        s shouldEqual "Hello"
        t shouldEqual " big world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
    pfun repairFrom ProgramFormula.StringInsert("Hello big ","","world") matchBody {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), va +& vb)) =>
        s shouldEqual "Hello big "
        t shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
    pfun repairFrom ProgramFormula.StringInsert("Hello ","", "world") matchBody {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), va +& vb)) =>
        s shouldEqual "Hello "
        t shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
  }

  test("Nested string delete") {
    val pfun = function(
      let("a"::StringType, "Hello big ")(av =>
        let("b"::StringType, "big ")(bv =>
          let("c"::StringType, "world")(cv =>
            av +& bv +& cv
          )
        )
      )
    )(inoxTypeOf[String])
    // "Hello big big world"
    pfun repairFrom ProgramFormula.StringInsert("Hello big",""," world") matchBody {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), Let(c, StringLiteral(u), va +& vb +& vc))) =>
        s shouldEqual "Hello big"
        t shouldEqual " "
        u shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
        vc shouldEqual c.toVariable
    }
    pfun repairFrom ProgramFormula.StringInsert("Hello ","","world") matchBody {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), Let(c, StringLiteral(u), va +& vb +& vc))) =>
        s shouldEqual "Hello "
        t shouldEqual ""
        u shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
        vc shouldEqual c.toVariable
    }
    pfun repairFrom ProgramFormula.StringInsert("Hello ","","ld") matchBody {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), Let(c, StringLiteral(u), va +& vb +& vc))) =>
        s shouldEqual "Hello "
        t shouldEqual ""
        u shouldEqual "ld"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
        vc shouldEqual c.toVariable
    }
  }

  test("Nested string delete direct") {
    val pfun = function(
      "Hello big " +& "big " +& "world"
    )(inoxTypeOf[String])
    // "Hello big big world"
    pfun repairFrom ProgramFormula.StringInsert("Hello big",""," world") matchBody {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello big"
        t shouldEqual " "
        u shouldEqual "world"
    }
    pfun repairFrom ProgramFormula.StringInsert("Hello ","","world") matchBody {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual ""
        u shouldEqual "world"
    }
    pfun repairFrom ProgramFormula.StringInsert("Hello ","","ld") matchBody {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual ""
        u shouldEqual "ld"
    }
  }

  test("String insert choice") {
    function(
      "\n" +& "Marion" +& ","
    )(inoxTypeOf[String]) repairFrom ProgramFormula.StringInsert("\n", "V", ",") matchBody {
      case StringLiteral("\n") +& StringLiteral("V") +& StringLiteral(",") =>
    }

    function(
      "\n" +& "M" +& "a"
    )(inoxTypeOf[String]) repairFrom ProgramFormula.StringInsert("\n", "V", "a") matchBody {
      case StringLiteral("\n") +& StringLiteral("V") +& StringLiteral("a") =>
    }

    val pfun = function(
      "(" +& "en" +& ")"
    )(inoxTypeOf[String])
    val pfun2 = pfun repairFrom ProgramFormula.StringInsert("(","f",")")
    pfun2 matchBody {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "("
        t shouldEqual "f"
        u shouldEqual ")"
    }
    pfun2 repairFrom ProgramFormula.StringInsert("(f","r",")") matchBody {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "("
        t shouldEqual "fr"
        u shouldEqual ")"
    }
  }

  /*test("Split / Clone and paste") {
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
  }*/

  test("Clone") {

  }

  test("Cut") {

  }
}
