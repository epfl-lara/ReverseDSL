package perfect
import inox._
import inox.trees.{not => dnot, _}
import inox.trees.dsl._
import org.scalatest._
import matchers._
import Matchers.{=== => _, _}
import perfect.ProgramFormula.CloneTextMultiple

/**
  * Created by Mikael on 27/03/2017.
  */
class CloneCutWrapTest extends FunSuite with TestHelpers {
  import InoxConvertible._
  import XmlTrees._
  import StringConcatExtended._
  import ProgramFormula.CloneText
  import semanticlenses._
  import core.predef.AssociativeInsert
  implicit val symbols = Utils.defaultSymbols

  test("Formula assignment") {
    val va = variable[String]("a")
    val vb = variable[String]("b")
    val vc = variable[String]("c")
    val f = Formula(Map(vc -> StrongValue(vb +& "42"), va -> StrongValue(vc +& vb), vb -> OriginalValue(StringLiteral("17"))))
    f.assignments match {
      case None => fail(s"Could not extract assignments from $f")
      case Some(f) => f(va) shouldEqual Let(vb.toVal, "17", Let(vc.toVal, vb +& "42", Let(va.toVal, vc +& vb, va)))
    }
    val f2 = Formula(Map(vc -> StrongValue(vb +& "42"), vb -> StrongValue(vc +& va), va -> OriginalValue(StringLiteral("17"))))
    f2.assignments shouldEqual None
  }
  test("Wrap") {
    val output = _Node("i", children=_List[Node](_Node("Hello")))
    val pfun =
      let("ad" :: String, "Hello"){ av =>
        _Node("i", children=_List[Node](_Node(av)))
      }
    pfun shouldProduce output

    val newOut = TreeWrap(output, v => _Node("b", children=_List[Node](v)))

    pfun repairFrom newOut shouldProduce {
      _Node("b", children=_List[Node](_Node("i", children=_List[Node](_Node("Hello")))))
    } match {
      case Let(ad, StringLiteral("Hello"), e) =>
        exprOps.variablesOf(e) should contain(ad.toVariable)
    }
  }

  test("Clone node") {
    // TODO
  }

  test("Insert node") {
    // TODO
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

  test("Tree modification without accelerator") {
    val output = _Node("b", children=_List[Node](_Node("i", children=_List[Node](_Node("Hello")))))
    val pfun =
      let("ad" :: inoxTypeOf[Node], _Node("Hello")){ av =>
        _Node("b", children=_List[Node](_Node("i", children=_List[Node](av))))
      }
    pfun shouldProduce output
    implicit val symbols = Utils.defaultSymbols
    val newOut = _Node("b", children=_List[Node](_Node("i", children=_List[Node](_Node("Good morning")))))

    pfun repairFrom newOut shouldProduce {
      _Node("b", children = _List[Node](_Node("i", children = _List[Node](_Node("Good morning")))))
    } match {
      case Let(ad, ADT(ADTType(Utils.xmlNode, Seq()), Seq(StringLiteral("Good morning"), _, _)), e) =>
        exprOps.variablesOf(e) should contain(ad.toVariable)
    }
  }

  test("Tree modification") {
    val output = _Node("b", children=_List[Node](_Node("i", children=_List[Node](_Node("Hello")))))
    val pfun =
      let("ad" :: inoxTypeOf[Node], _Node("Hello")){ av =>
        _Node("b", children=_List[Node](_Node("i", children=_List[Node](av))))
      }
    pfun shouldProduce output
    implicit val symbols = Utils.defaultSymbols
    val newOut = TreeModification(
      output,
      "Good morning",
      List(Utils.children, Utils.head, Utils.children, Utils.head, Utils.tag)
    )

    pfun repairFrom newOut shouldProduce {
      _Node("b", children=_List[Node](_Node("i", children=_List[Node](_Node("Good morning")))))
    } match {
      case Let(ad, ADT(ADTType(Utils.xmlNode, Seq()), Seq(StringLiteral("Good morning"), _, _)), e) =>
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

    pfun repairFrom StringInsert("Hello ", "big", " world", AssociativeInsert.InsertToLeft) match {
      case Let(a, StringLiteral("Hello big"), Let(b, StringLiteral(" world"), va +& vb)) =>
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
    pfun repairFrom StringInsert("Hello ", "big", " world", AssociativeInsert.InsertToRight) match {
      case Let(a, StringLiteral("Hello "), Let(b, StringLiteral("big world"), va +& vb)) =>
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }

    pfun repairFrom StringInsert("Hello", " big", "  world", AssociativeInsert.InsertAutomatic) match {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), va +& vb)) =>
        s shouldEqual "Hello big "
        t shouldEqual " world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
    pfun repairFrom StringInsert("Hello  ", "big ", "world", AssociativeInsert.InsertAutomatic) match {
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

    pfun repairFrom StringInsert("Hello big", " big", " world", AssociativeInsert.InsertAutomatic) match {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), Let(c, StringLiteral(u), va +& vb +& vc))) =>
        s shouldEqual "Hello "
        t shouldEqual "big big "
        u shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
        vc shouldEqual c.toVariable
    }
    pfun repairFrom StringInsert("Hello"," big"," big world", AssociativeInsert.InsertAutomatic) match {
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

    pfun repairFrom StringInsert("Hello big", " big", " world", AssociativeInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual "big big "
        u shouldEqual "world"
    }
    pfun repairFrom StringInsert("Hello"," big"," big world", AssociativeInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello big "
        t shouldEqual "big "
        u shouldEqual "world"
    }
  }

  test("String insert direct test space weight") {
    val pfun = "Hello " +& "world"

    pfun repairFrom StringInsert("Hello ", " ", "world", AssociativeInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello  "
        t shouldEqual "world"
    }
    pfun repairFrom StringInsert("Hello ", " ", "world", AssociativeInsert.InsertToRight) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello "
        t shouldEqual " world"
    }
    pfun repairFrom StringInsert("Hello ", "big", "world", AssociativeInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello "
        t shouldEqual "bigworld"
    }
    pfun repairFrom StringInsert("Hello ", "big", "world", AssociativeInsert.InsertToLeft) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello big"
        t shouldEqual "world"
    }

    val pfun2 = "Hello" +& " world"

    pfun2 repairFrom StringInsert("Hello", " ", " world", AssociativeInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello"
        t shouldEqual "  world"
    }
    pfun2 repairFrom StringInsert("Hello", " ", " world", AssociativeInsert.InsertToLeft) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello "
        t shouldEqual " world"
    }
    pfun2 repairFrom StringInsert("Hello", "big", " world", AssociativeInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hellobig"
        t shouldEqual " world"
    }
    pfun2 repairFrom StringInsert("Hello", "big", " world", AssociativeInsert.InsertToRight) match {
      case StringLiteral(s) +& StringLiteral(t) =>
        s shouldEqual "Hello"
        t shouldEqual "big world"
    }
  }

  test("Nested string modification direct") {
    val pfun = "Hello " +& "big " +& "world"

    pfun repairFrom StringInsert("Hello big ","change","", AssociativeInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual "big "
        u shouldEqual "change"
    }

    pfun repairFrom StringInsert("","Good afternoon ","big world", AssociativeInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Good afternoon "
        t shouldEqual "big "
        u shouldEqual "world"
    }

    pfun repairFrom StringInsert("Hello ","great"," world", AssociativeInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual "great "
        u shouldEqual "world"
    }

    repairProgramList(pfun, StringInsert("Hello", ", amazing", " world", AssociativeInsert.InsertAutomatic), 2).take(2).toList.map(x => x match {
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
    pfun repairFrom StringInsert("Hello",""," big world", AssociativeInsert.InsertAutomatic) match {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), va +& vb)) =>
        s shouldEqual "Hello"
        t shouldEqual " big world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
    pfun repairFrom StringInsert("Hello big ","","world", AssociativeInsert.InsertAutomatic) match {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), va +& vb)) =>
        s shouldEqual "Hello big "
        t shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
    }
    pfun repairFrom StringInsert("Hello ","", "world", AssociativeInsert.InsertAutomatic) match {
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
    pfun repairFrom StringInsert("Hello big",""," world", AssociativeInsert.InsertAutomatic) match {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), Let(c, StringLiteral(u), va +& vb +& vc))) =>
        s shouldEqual "Hello big"
        t shouldEqual " "
        u shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
        vc shouldEqual c.toVariable
    }
    pfun repairFrom StringInsert("Hello ","","world", AssociativeInsert.InsertAutomatic) match {
      case Let(a, StringLiteral(s), Let(b, StringLiteral(t), Let(c, StringLiteral(u), va +& vb +& vc))) =>
        s shouldEqual "Hello "
        t shouldEqual ""
        u shouldEqual "world"
        va shouldEqual a.toVariable
        vb shouldEqual b.toVariable
        vc shouldEqual c.toVariable
    }
    pfun repairFrom StringInsert("Hello ","","ld", AssociativeInsert.InsertAutomatic) match {
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
    pfun repairFrom StringInsert("Hello big",""," world", AssociativeInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello big"
        t shouldEqual " "
        u shouldEqual "world"
    }
    pfun repairFrom StringInsert("Hello ","","world", AssociativeInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual ""
        u shouldEqual "world"
    }
    pfun repairFrom StringInsert("Hello ","","ld", AssociativeInsert.InsertAutomatic) match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "Hello "
        t shouldEqual ""
        u shouldEqual "ld"
    }
  }

  test("String insert choice") {
    "\n" +& "Marion" +& "," repairFrom StringInsert("\n", "V", ",", AssociativeInsert.InsertAutomatic) match {
      case StringLiteral("\n") +& StringLiteral("V") +& StringLiteral(",") =>
    }

    "\n" +& "M" +& "a" repairFrom StringInsert("\n", "V", "a", AssociativeInsert.InsertAutomatic) match {
      case StringLiteral("\n") +& StringLiteral("V") +& StringLiteral("a") =>
    }

    val pfun = "(" +& "en" +& ")"
    val pfun2 = pfun repairFrom StringInsert("(","f",")", AssociativeInsert.InsertAutomatic)
    pfun2 match {
      case StringLiteral(s) +& StringLiteral(t) +& StringLiteral(u) =>
        s shouldEqual "("
        t shouldEqual "f"
        u shouldEqual ")"
    }
    pfun2 repairFrom StringInsert("(f","r",")", AssociativeInsert.InsertAutomatic) match {
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
      StringConcats(List(StringLiteral("I "), like2: Variable, StringLiteral(" to"), move2: Variable, StringLiteral("!"))))) =>
        move.id shouldEqual move2.id
        like.id shouldEqual like2.id
    }
  }

  test("Clone an existing variable") { // can we return the original variable instead of inserting a new one?
    val pfun:Expr = let("mikael"::StringType, "Mikael")(mikael => "I am " +& mikael +& " the great ")

    val cloneVar = variable[String]("clone")

    val pfun2 = pfun repairFrom CloneText("I am ", "Mikael", " the great ", cloneVar) shouldProduce StringLiteral("I am Mikael the great ")

    pfun2 match {
      case Let(cloned, v, body) =>
        val pfun3 = updateBody(pfun2) {
          case c1 +& mikael +& c2 => c1 +& mikael +& c2 +& cloned.toVariable
        }
        Utils.simplifyClones(pfun3, cloned.toVariable) match {
          case Some((cl, Let(cloned, v, c1 +& clonedV +& c2 +& clonedV2)))
            if cloned.toVariable == clonedV && clonedV2 == clonedV && clonedV == cl =>
        }
    }
  }

  test("Add space after clone (wrap string)") {
    val pfun:Expr = let("move_it"::StringType, "move it")(move_it => "I like to "+&move_it)

    repairProgramList(pfun, StringInsert("I like to move it", " ", "", AssociativeInsert.InsertAutomatic), 2).take(2).map{
      case Let(p, StringLiteral("move it"), body) => 1
      case Let(p, StringLiteral("move it "), body) => 2
    }.sum shouldEqual 3
  }

  test("Clone basic") {
    val pfun:Expr = "Test"
    pfun repairFrom CloneTextMultiple("Test", Nil) shouldProduce StringLiteral("Test")
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
    val pfun =  let("moveit"::String, "move it ")(moveit =>
        "I like to " +& moveit +& "like that")

    (pfun repairFrom CloneText("I like ", "to move", " it like that") match {
      case Let(c1, StringLiteral("to "), Let(c2, StringLiteral("move"), body)) => (c1, c2, body)
      case Let(c2, StringLiteral("move"), Let(c1, StringLiteral("to "), body)) => (c1, c2, body)
    }) match { case (cto, cmove,
          Let(cloned, cto1 +& cmove1,
          Let(moveit, cmove2 +& StringLiteral(" it "),
          StringLiteral("I like ") +& cto2 +& moveit1 +& StringLiteral("like that")))) =>
          cto.toVariable shouldEqual cto1
          cmove.toVariable shouldEqual cmove1
          cmove2 shouldEqual cmove1
          cto2 shouldEqual cto1
          moveit1 shouldEqual moveit.toVariable
    }
  }

  test("Clone accross a StringConcat of different variables") {
    val pfun = let("likethat"::String, "like that")(likethat =>
      let("moveit"::String, "move it ")(moveit =>
        moveit +& likethat))

    (pfun repairFrom CloneText("move ","it like"," that") match { // We don't have control on how the variables are inserted.
      case Let(c1, StringLiteral("it "), Let(c2, StringLiteral("like"), b)) => (c1, c2, b)
      case Let(c2, StringLiteral("like"), Let(c1, StringLiteral("it "), b)) => (c1, c2, b) }) match {
      case (c1, c2, Let(cloned, cv1 +& cv2,
      Let(likethat, cv22 +& StringLiteral(" that"),
      Let(moveit, StringLiteral("move ") +&cv11 ,
      (moveit1: Variable) +& (likethat1: Variable) )))) =>
        c1.toVariable shouldEqual cv1
        c2.toVariable shouldEqual cv2
        cv11 shouldEqual cv1
        cv22 shouldEqual cv2
        moveit.id shouldEqual moveit1.id
        likethat.id shouldEqual likethat1.id
    }
  }

  test("Clone accross a StringConcat of same variables") {
    val pfun = let("move"::String, "move it ")(move => move +& move)

    (pfun repairFrom CloneText("move ", "it move", " it ") match { // We don't have control on how the variables are inserted.
      case Let(c1, StringLiteral("it "), Let(c2, StringLiteral("move"), b)) => (c1, c2, b)
      case Let(c2, StringLiteral("move"), Let(c1, StringLiteral("it "), b)) => (c1, c2, b)
    }) match {
      case (c1, c2, Let(cloned, cv1 +& cv2, Let(move, cv22 +& StringLiteral(" ") +& cv11,
      (move1: Variable) +& (move2: Variable)))) =>
        c1.toVariable shouldEqual cv1
        c2.toVariable shouldEqual cv2
        cv11 shouldEqual cv1
        cv22 shouldEqual cv2
        move1 shouldEqual move2
        move.id shouldEqual move1.id
    }
  }

  def updateBody(e: Expr)(f: Expr => Expr): Expr = e match {
    case Let(a, b, c) => Let(a, b, updateBody(c)(f))
    case c => f(c)
  }

  test("Clone accross a StringConcat of same variables but wider") {
    val pfun = let("move"::String, "move it ")(move => move +& move)

    val ct@ProgramFormula(CloneTextMultiple.Goal(_, (_, cloned, _)::Nil), _) = CloneText("move", " it move ", "it ")
    val pfun2 = pfun repairFrom ct shouldProduce StringLiteral("move it move it ")

    val pfun3 = updateBody(pfun2){
      case moveVar +& moveVar2 => moveVar +& moveVar2 +& cloned
    }
    pfun3 shouldProduce StringLiteral("move it move it  it move ")
    pfun3 repairFrom StringInsert("move it move i", "f", "  it move ", AssociativeInsert.InsertAutomatic) shouldProduce
      StringLiteral("move if move if  if move ")
  }

  test("Clone accross a StringConcat of same variables with identical overlap") {
    val pfun = let("move"::String, "mov it ")(move => move +& move +& move)

    val ct@ProgramFormula(CloneTextMultiple.Goal(_, (_, cloned, _)::Nil), _) = CloneText("mov ", "it mov it mov ", "it ")
    val pfun2 = pfun repairFrom ct shouldProduce StringLiteral("mov it mov it mov it ")
    val pfun3 = updateBody(pfun2){
      case moveVar +& moveVar2 +& moveVar3 => moveVar +& moveVar2 +& moveVar3 +& cloned
    }
    pfun3 shouldProduce StringLiteral("mov it mov it mov it it mov it mov ")
    pfun3 repairFrom StringInsert("mov it mov ", "a", "t mov it it mov it mov ", AssociativeInsert.InsertAutomatic) shouldProduce
      StringLiteral("mov at mov at mov at at mov at mov ")
  }

  import semanticlenses.PasteVariable
  test("Paste") {
    val pfun: Let = let("v"::String, " move it")(v => "I like to" +& v +& "!")
    val v = pfun.vd.toVariable

    pfun repairFrom PasteVariable("I like to move it", v, " move it", "!", AssociativeInsert.InsertToLeft) match {
      case Let(vd, StringLiteral(s), StringLiteral(a) +& ((v: Variable) +& (v2: Variable)) +& StringLiteral(b)) =>
        v shouldEqual v2
        v.id shouldEqual vd.id
        s shouldEqual " move it"
        a shouldEqual "I like to"
        b shouldEqual "!"
    }

    pfun repairFrom PasteVariable("I like to move it", v, " move it", "!", AssociativeInsert.InsertToRight) match {
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

    val pfun2 = pfun repairFrom PasteVariable("I like to move", like, " like", " it!", AssociativeInsert.InsertAutomatic) match {
      case l@Let(like, StringLiteral(like_s),
      Let(move_it, StringLiteral(" move") +& (like2: Variable) +& StringLiteral(" it"),
      StringLiteral("I") +& (like3: Variable) +& StringLiteral(" to") +& (move_it2: Variable) +& StringLiteral("!"))) =>
        like.toVariable shouldEqual like3
        move_it.toVariable shouldEqual move_it2
        like2 shouldEqual like3
        l
    }
    pfun2 repairFrom StringInsert("I like to move", " ", " like it!", AssociativeInsert.InsertToLeft) match {
      case l@Let(like, StringLiteral(like_s),
      Let(move_it, StringLiteral(" move ") +& (like2: Variable) +& StringLiteral(" it"),
      StringLiteral("I") +& (like3: Variable) +& StringLiteral(" to") +& (move_it2: Variable) +& StringLiteral("!"))) =>
        like.toVariable shouldEqual like3
        move_it.toVariable shouldEqual move_it2
        like2 shouldEqual like3
    }
  }

  test("Clone and paste tricky") {
    val pfun: Expr =
      let("ab"::String, "ab")(ab =>
        let("x"::String, ab)(x =>
          x +& x
        )
      )

    val expected = "abab"

    pfun shouldProduce expected

    val v = variable[String]("cloned")
    val pfun2 = pfun repairFrom CloneText("ab", "ab", "", v) shouldProduce expected

    exprOps.count {
      case Let(vd, _, _) if vd.toVariable == v => 1
      case _ => 0
    }(pfun2) shouldEqual 1
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
