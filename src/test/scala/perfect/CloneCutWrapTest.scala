package perfect
import inox._
import inox.trees._
import inox.trees.dsl._
import org.scalatest._
import matchers._
import Matchers.{=== => _, _}

/**
  * Created by Mikael on 27/03/2017.
  */
class CloneCutWrapTest extends FunSuite with TestHelpers {
  import InoxConvertible._
  import XmlTrees._
  import StringConcatExtended._
  import ProgramFormula.{StringInsert, ListInsert, TreeWrap, TreeUnwrap, CloneText, PasteVariable}

  test("Formula assignment") {
    val va = variable[String]("a")
    val vb = variable[String]("b")
    val vc = variable[String]("c")
    val f = Formula(BooleanLiteral(true) && (vb +& "42") === vc && va === (vc +& vb) && vb === "17")
    f.assignments match {
      case None => fail(s"Could not extract assignments from $f")
      case Some(f) => f(va) shouldEqual Let(vb.toVal, "17", Let(vc.toVal, vb +& "42", Let(va.toVal, vc +& vb, va)))
    }
    val f2 = Formula(BooleanLiteral(true) && (vb +& "42") === va && va === (vc +& vb) && vb === "17")
    f2.assignments shouldEqual None
  }
  test("Wrap") {
    val output = _Node("i", children=_List[Node](_Node("Hello")))
    val pfun =
      let("ad" :: String, "Hello"){ av =>
        _Node("i", children=_List[Node](_Node(av)))
      }
    pfun shouldProduce output

    val newOut = TreeWrap(output, v => _Node("b", children=_List[Node](v)))(Utils.defaultSymbols)

    pfun repairFrom newOut shouldProduce {
      _Node("b", children=_List[Node](_Node("i", children=_List[Node](_Node("Hello")))))
    } match {
      case Let(ad, StringLiteral("Hello"), e) =>
        exprOps.variablesOf(e) should contain(ad.toVariable)
    }
  }

  /*test("Unwrap") {
    val output = _Node("b", children=_List[Node](_Node("i", children=_List[Node](_Node("Hello")))))
    val pfun =
      let("ad" :: String, "Hello"){ av =>
        _Node("b", children=_List[Node](_Node("i", children=_List[Node](_Node(av)))))
      }
    pfun shouldProduce output

    val newOut = TreeUnwrap(
      Node,
      output,
      List(Utils.children, Utils.head)
    )

    pfun repairFrom newOut shouldProduce {
      _Node("i", children=_List[Node](_Node("Hello")))
    } match {
      case Let(ad, StringLiteral("Hello"), e) =>
        exprOps.variablesOf(e) should contain(ad.toVariable)
    }
  }*/

  test("String insert") {
    val pfun =
      let("a"::String, "Hello ")(av =>
        let("b"::String, " world")(bv =>
          av +& bv
        )
      )

    pfun repairFrom StringInsert("Hello ", "big", " world", StringInsert.InsertToLeft) match {
      case Let(a, StringLiteral("Hello big"), Let(b, StringLiteral(" world"), va +& vb)) =>
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
    pfun repairFrom StringInsert("Hello ", "big", " world", StringInsert.InsertToRight) match {
      case Let(a, StringLiteral("Hello "), Let(b, StringLiteral("big world"), va +& vb)) =>
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }

    pfun repairFrom StringInsert("Hello", " big", "  world", StringInsert.InsertAutomatic) match {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), va +& vb)) =>
        s shouldEqual "Hello big "
        t shouldEqual " world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
    pfun repairFrom StringInsert("Hello  ", "big ", "world", StringInsert.InsertAutomatic) match {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), va +& vb)) =>
        s shouldEqual "Hello "
        t shouldEqual " big world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
  }

  test("Nested string insert") {
    val pfun =
      let("a"::StringType, "Hello ")(av =>
        let("b"::StringType, "big ")(bv =>
          let("c"::StringType, "world")(cv =>
            av +& bv +& cv
          )
        )
      )

    pfun repairFrom StringInsert("Hello big", " big", " world", StringInsert.InsertAutomatic) match {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), Let(c, StringLiteral(u), va +& vb +& vc))) =>
        s shouldEqual "Hello "
        t shouldEqual "big big "
        u shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
        vc shouldEqual c.toVariable
    }
    pfun repairFrom StringInsert("Hello"," big"," big world", StringInsert.InsertAutomatic) match {
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
    val pfun = "Hello " +& "big " +& "world"

    pfun repairFrom StringInsert("Hello big", " big", " world", StringInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual "big big "
        u shouldEqual "world"
    }
    pfun repairFrom StringInsert("Hello"," big"," big world", StringInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello big "
        t shouldEqual "big "
        u shouldEqual "world"
    }
  }

  test("String insert direct test space weight") {
    val pfun = "Hello " +& "world"

    pfun repairFrom StringInsert("Hello ", " ", "world", StringInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello  "
        t shouldEqual "world"
    }
    pfun repairFrom StringInsert("Hello ", " ", "world", StringInsert.InsertToRight) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello "
        t shouldEqual " world"
    }
    pfun repairFrom StringInsert("Hello ", "big", "world", StringInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello "
        t shouldEqual "bigworld"
    }
    pfun repairFrom StringInsert("Hello ", "big", "world", StringInsert.InsertToLeft) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello big"
        t shouldEqual "world"
    }

    val pfun2 = "Hello" +& " world"

    pfun2 repairFrom StringInsert("Hello", " ", " world", StringInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello"
        t shouldEqual "  world"
    }
    pfun2 repairFrom StringInsert("Hello", " ", " world", StringInsert.InsertToLeft) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello "
        t shouldEqual " world"
    }
    pfun2 repairFrom StringInsert("Hello", "big", " world", StringInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hellobig"
        t shouldEqual " world"
    }
    pfun2 repairFrom StringInsert("Hello", "big", " world", StringInsert.InsertToRight) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello"
        t shouldEqual "big world"
    }
  }

  test("Nested string modification direct") {
    val pfun = "Hello " +& "big " +& "world"

    pfun repairFrom StringInsert("Hello big ","change","", StringInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual "big "
        u shouldEqual "change"
    }

    pfun repairFrom StringInsert("","Good afternoon ","big world", StringInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Good afternoon "
        t shouldEqual "big "
        u shouldEqual "world"
    }

    pfun repairFrom StringInsert("Hello ","great"," world", StringInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual "great "
        u shouldEqual "world"
    }

    repairProgramList(pfun, StringInsert("Hello", ", amazing", " world", StringInsert.InsertAutomatic), 2).take(2).toList.map(x => x match {
      case StringLiteral("Hello, amazing") +& StringLiteral(" ") +& StringLiteral("world") =>
        1
      case StringLiteral("Hello") +& StringLiteral(", amazing ") +& StringLiteral("world") =>
        2
    }).sum shouldEqual 3

  }

  test("String delete") {
    val pfun =
      let("a"::StringType, "Hello big ")(av =>
        let("b"::StringType, " big world")(bv =>
          av +& bv
        )
      )
    // "Hello big  big world"
    pfun repairFrom StringInsert("Hello",""," big world", StringInsert.InsertAutomatic) match {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), va +& vb)) =>
        s shouldEqual "Hello"
        t shouldEqual " big world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
    pfun repairFrom StringInsert("Hello big ","","world", StringInsert.InsertAutomatic) match {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), va +& vb)) =>
        s shouldEqual "Hello big "
        t shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
    pfun repairFrom StringInsert("Hello ","", "world", StringInsert.InsertAutomatic) match {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), va +& vb)) =>
        s shouldEqual "Hello "
        t shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
  }

  test("Nested string delete") {
    val pfun =
      let("a"::StringType, "Hello big ")(av =>
        let("b"::StringType, "big ")(bv =>
          let("c"::StringType, "world")(cv =>
            av +& bv +& cv
          )
        )
      )
    // "Hello big big world"
    pfun repairFrom StringInsert("Hello big",""," world", StringInsert.InsertAutomatic) match {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), Let(c, StringLiteral(u), va +& vb +& vc))) =>
        s shouldEqual "Hello big"
        t shouldEqual " "
        u shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
        vc shouldEqual c.toVariable
    }
    pfun repairFrom StringInsert("Hello ","","world", StringInsert.InsertAutomatic) match {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), Let(c, StringLiteral(u), va +& vb +& vc))) =>
        s shouldEqual "Hello "
        t shouldEqual ""
        u shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
        vc shouldEqual c.toVariable
    }
    pfun repairFrom StringInsert("Hello ","","ld", StringInsert.InsertAutomatic) match {
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
    val pfun = "Hello big " +& "big " +& "world"
    // "Hello big big world"
    pfun repairFrom StringInsert("Hello big",""," world", StringInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello big"
        t shouldEqual " "
        u shouldEqual "world"
    }
    pfun repairFrom StringInsert("Hello ","","world", StringInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual ""
        u shouldEqual "world"
    }
    pfun repairFrom StringInsert("Hello ","","ld", StringInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual ""
        u shouldEqual "ld"
    }
  }

  test("String insert choice") {
    "\n" +& "Marion" +& "," repairFrom StringInsert("\n", "V", ",", StringInsert.InsertAutomatic) match {
      case StringLiteral("\n") +& StringLiteral("V") +& StringLiteral(",") =>
    }

    "\n" +& "M" +& "a" repairFrom StringInsert("\n", "V", "a", StringInsert.InsertAutomatic) match {
      case StringLiteral("\n") +& StringLiteral("V") +& StringLiteral("a") =>
    }

    val pfun = "(" +& "en" +& ")"
    val pfun2 = pfun repairFrom StringInsert("(","f",")", StringInsert.InsertAutomatic)
    pfun2 match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "("
        t shouldEqual "f"
        u shouldEqual ")"
    }
    pfun2 repairFrom StringInsert("(f","r",")", StringInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "("
        t shouldEqual "fr"
        u shouldEqual ")"
    }
  }

  test("Clone") {
    val pfun: Expr = "I like to move it!"
    pfun repairFrom CloneText("I like to", " move it", "!") match {
      case Let(vd, StringLiteral(s), StringLiteral(a) +& (v: Variable) +& StringLiteral(b)) =>
        vd.id shouldEqual v.id
        a shouldEqual "I like to"
        s shouldEqual " move it"
        b shouldEqual "!"
    }
  }

  test("Paste") {
    val pfun: Let = let("v"::String, " move it")(v => "I like to" +& v +& "!")
    val v = pfun.vd.toVariable

    pfun repairFrom PasteVariable("I like to move it", v, " move it", "!", PasteVariable.PasteToLeft) match {
      case Let(vd, StringLiteral(s), StringLiteral(a) +& ((v: Variable) +& (v2: Variable)) +& StringLiteral(b)) =>
        v shouldEqual v2
        v.id shouldEqual vd.id
        s shouldEqual " move it"
        a shouldEqual "I like to"
        b shouldEqual "!"
    }

    pfun repairFrom PasteVariable("I like to move it", v, " move it", "!", PasteVariable.PasteToRight) match {
      case Let(vd, StringLiteral(s), StringLiteral(a) +& (v: Variable) +& ((v2: Variable) +& StringLiteral(b))) =>
        v shouldEqual v2
        v.id shouldEqual vd.id
        s shouldEqual " move it"
        a shouldEqual "I like to"
        b shouldEqual "!"
    }
  }

  test("Cut") {

  }
}
