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

  test("Home-made list map") {
    val mpDef = ReverseProgram.RecLens.build("map",
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


    val prog = let("mp"::inoxTypeOf[(List[String], String => String) => List[String]], mpDef)(mp =>
      mp(_List[String]("brother", "boss"), \("s"::String)(s => "Big " +& s))
    )
    prog shouldProduce _List[String]("Big brother", "Big boss")
    prog repairFrom _List[String]("Big brothers", "Big boss") match {
      case Let(mpd, mpval, Application(mpv, Seq(l, Lambda(Seq(i), StringConcat(StringLiteral("Big "), iv))))) =>
        mpv shouldEqual mpd.toVariable
        l shouldEqual _List[String]("brothers", "boss")
    }
  }
}
