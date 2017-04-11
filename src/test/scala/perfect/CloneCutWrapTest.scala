package perfect
import inox._
import inox.trees.{not => dnot, _}
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

  test("Unwrap") {
    val output = _Node("b", children=_List[Node](_Node("i", children=_List[Node](_Node("Hello")))))
    val pfun =
      let("ad" :: String, "Hello"){ av =>
        _Node("b", children=_List[Node](_Node("i", children=_List[Node](_Node(av)))))
      }
    pfun shouldProduce output

    val newOut = TreeUnwrap(
      inoxTypeOf[Node],
      output,
      List(Utils.children, Utils.head)
    )

    pfun repairFrom newOut shouldProduce {
      _Node("i", children=_List[Node](_Node("Hello")))
    } match {
      case Let(ad, StringLiteral("Hello"), e) =>
        exprOps.variablesOf(e) should contain(ad.toVariable)
    }
  }

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
      case Let(vd, StringLiteral(" move it"), StringLiteral("I like to") +& (v: Variable) +& StringLiteral("!")) =>
        vd.id shouldEqual v.id
    }
  }

  test("Clone another constant part of a concatenation") {
    val pfun: Expr = let("v"::String, " move it")(v => "I like to" +& v +& "!")
    pfun repairFrom CloneText("I ", "like", " to move it!") match {
      case Let(like, StringLiteral("like"), Let(move, StringLiteral(" move it"),
      (StringLiteral("I ") +& (like2: Variable) +& StringLiteral(" to") +& (move2: Variable)) +& StringLiteral("!"))) =>
        move.id shouldEqual move2.id
        like.id shouldEqual like2.id
    }
  }

  test("Clone an existing variable") {

  }


  test("Clone accross a StringConcat of constants") {
    val pfun = ("I like" +& " to ") +& ("move" +& " it!")
    pfun repairFrom CloneText("I like ", "to move", " it!") match { // We don't have control on how the variables are inserted.
      case Let(c1, StringLiteral("to "), Let(c2, StringLiteral("move"), Let(cloned, cv1 +& cv2,
      (StringLiteral("I like") +& (StringLiteral(" ") +& cv11)) +& (cv22 +& StringLiteral(" it!"))))) =>
        c1.toVariable shouldEqual cv1
        c2.toVariable shouldEqual cv2
        cv1 shouldEqual cv11
        cv2 shouldEqual cv22
        c1.id.toString should not equal cloned.id.toString
      case Let(c2, StringLiteral("move"), Let(c1, StringLiteral("to "), Let(cloned, cv1 +& cv2,
      (StringLiteral("I like") +& (StringLiteral(" ") +& cv11)) +& (cv22 +& StringLiteral(" it!"))))) =>
        c1.toVariable shouldEqual cv1
        c2.toVariable shouldEqual cv2
        cv1 shouldEqual cv11
        cv2 shouldEqual cv22
        c1.id.toString should not equal cloned.id.toString
    }
  }

  test("Clone accross a StringConcat of constant/variable") {

  }

  test("Clone accross a StringConcat of variables") {

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

  test("Paste inside a variable") {
    val pfun: Let =
      let("k"::String, " like")(like =>
        let("v"::String, " move it")(move_it =>
        "I"+& like +& " to" +& move_it +& "!"))
    val like = pfun.vd.toVariable

    val pfun2 = pfun repairFrom PasteVariable("I like to move", like, " like", " it!", PasteVariable.PasteAutomatic) match {
      case l@Let(like, StringLiteral(like_s),
      Let(move_it, StringLiteral(" move") +& (like2: Variable) +& StringLiteral(" it"),
      StringLiteral("I") +& (like3: Variable) +& StringLiteral(" to") +& (move_it2: Variable) +& StringLiteral("!"))) =>
        like.toVariable shouldEqual like3
        move_it.toVariable shouldEqual move_it2
        like2 shouldEqual like3
        l
    }
    pfun2 repairFrom StringInsert("I like to move", " ", " like it!", StringInsert.InsertToLeft) match {
      case l@Let(like, StringLiteral(like_s),
      Let(move_it, StringLiteral(" move ") +& (like2: Variable) +& StringLiteral(" it"),
      StringLiteral("I") +& (like3: Variable) +& StringLiteral(" to") +& (move_it2: Variable) +& StringLiteral("!"))) =>
        like.toVariable shouldEqual like3
        move_it.toVariable shouldEqual move_it2
        like2 shouldEqual like3
        l
    }
  }

  /*test("Paste inside a variable and reverse order.") {
    val pfun: Let =
        let("v"::String, " move it")(move_it =>
          let("k"::String, " like")(like =>
          "I"+& like +& " to" +& move_it +& "!"))
    val like = pfun.vd.toVariable

    pfun repairFrom PasteVariable("I like to move", like, " like", " it!", PasteVariable.PasteAutomatic) match {
      case Let(like, StringLiteral(like_s),
      Let(move_it, StringLiteral(" move") +& (like2: Variable) +& StringLiteral(" it"),
      StringLiteral("I") +& (like3: Variable) +& StringLiteral(" to") +& (move_it2: Variable) +& StringLiteral("!"))) =>
        like.toVariable shouldEqual like3
        move_it.toVariable shouldEqual move_it2
        like2 shouldEqual like3
    }
  }*/

  /*test("Paste Recursive ?") {
    val pfun: Let = let("v"::String, " move it")(v => "I like to" +& v +& "!")
    val v = pfun.vd.toVariable

    pfun repairFrom PasteVariable("I like to move", v, " move it", " it!", PasteVariable.PasteToLeft) match {
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
  }*/

  test("Cut") {

  }
}
