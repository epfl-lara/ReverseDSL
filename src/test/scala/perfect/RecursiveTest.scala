package perfect

import inox._
import inox.trees.{not => dnot, _}
import inox.trees.dsl._
import org.scalatest._
import matchers._
import Matchers.{=== => _, _}

/**
  * Created by Mikael on 03/05/2017.
  */
class RecursiveTest extends FunSuite with TestHelpers {
  import InoxConvertible._
  import Utils._
  import StringConcatExtended._
  import semanticlenses._
  import core.predef.AssociativeInsert
  implicit val symbols = Utils.defaultSymbols

  val mapDef = lenses.Lenses.RecLens.build("map",
    "l"::inoxTypeOf[List[String]], "f"::inoxTypeOf[String => String])(inoxTypeOf[List[String]])((mprec, ls, f) =>
    if_(ls.isInstOf(TCons[String])) {
      let("c"::TCons[String], ls.asInstOf(TCons[String]))(c =>
        let("head"::String, c.getField(head))( head =>
          ADT(TCons[String], Seq(Application(f, Seq(head)), mprec(c.getField(tail), f)))
        )
      )
    } else_ {
      _List[String]()
    })

  def filterDef = lenses.Lenses.RecLens.build("filter",
    "l"::inoxTypeOf[List[String]], "f"::inoxTypeOf[String => Boolean])(inoxTypeOf[List[String]])((filterrec, ls, f) =>
    if_(ls.isInstOf(TCons[String])) {
      let("c"::TCons[String], ls.asInstOf(TCons[String]))(c =>
        let("head"::String, c.getField(head))( head =>
          if_(Application(f, Seq(head))) {
            ADT(TCons[String], Seq(head, filterrec(c.getField(tail), f)))
          } else_ {
            filterrec(c.getField(tail), f)
          }
        )
      )
    } else_ {
      _List[String]()
    })

  test("Home-made list map inverse list") {
    val prog = let("mp"::inoxTypeOf[(List[String], String => String) => List[String]], mapDef)(mp =>
      mp(_List[String]("brother", "boss"), \("s"::String)(s => "Big " +& s))
    )
    prog shouldProduce _List[String]("Big brother", "Big boss")
    prog repairFrom _List[String]("Big brothers", "Big boss") match {
      case Let(mpd, mpval, Application(mpv, Seq(l, Lambda(Seq(i), StringConcat(StringLiteral("Big "), iv))))) =>
        mpv shouldEqual mpd.toVariable
        l shouldEqual _List[String]("brothers", "boss")
    }
  }
  test("Home-made list map inverse precise list modification") {
    val prog = let("mp"::inoxTypeOf[(List[String], String => String) => List[String]], mapDef)(mp =>
      mp(_List[String]("brother", "boss"), \("s"::String)(s => "Big " +& s))
    )
    val original = _List[String]("Big brother", "Big boss")
    val modified = StringInsert.Goal("Big brother", "s", "", AssociativeInsert.InsertAutomatic)
    prog shouldProduce original
    Log activated (prog repairFrom
      TreeModification(
        original,
        modified,
        List(Utils.head)
      )) match {
      case Let(mpd, mpval, Application(mpv, Seq(l, Lambda(Seq(i), StringConcat(StringLiteral("Big "), iv))))) =>
        mpv shouldEqual mpd.toVariable
        l shouldEqual _List[String]("brothers", "boss")
    }
  }
  test("Home-made list map inverse function") {
    val prog = let("mp"::inoxTypeOf[(List[String], String => String) => List[String]], mapDef)(mp =>
      mp(_List[String]("brother", "boss"), \("s"::String)(s => "Big " +& s))
    )
    prog shouldProduce _List[String]("Big brother", "Big boss")
    prog repairFrom _List[String]("Great brother", "Big boss") shouldProduce
    _List[String]("Great brother", "Great boss") match {
      case Let(mpd, mpval, Application(mpv, Seq(l, Lambda(Seq(i), StringConcat(StringLiteral("Great "), iv))))) =>
        mpv shouldEqual mpd.toVariable
        l shouldEqual _List[String]("brother", "boss")
    }
  }

  test("Home-made filter") {
    val prog = let("filter"::inoxTypeOf[(List[String], String => Boolean) => List[String]], filterDef)(filter =>
      filter(_List[String]("four", "lot of five", "six"), \("s"::String)(s => StringLength(s) < IntegerLiteral(5)))
    )

    prog shouldProduce _List[String]("four", "six")
    val goal = ListInsertGoal(List("four"), List("five"), List("six"))
    //val goal = _List[String]("four", "five", "six")

    Log activated println(repairProgramList(prog, goal, 3).take(3).map(eval).mkString("\n"))
  }

  //TODO: Test filter recursive.
}
