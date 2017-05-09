package perfect
import inox.FreshIdentifier
import legacy._
import org.scalatest.FunSuite
import perfect.WebTrees.Element
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
import perfect.semanticlenses._

/**
  * Created by Mikael on 22/03/2017.
  */
class BagMapSetTest extends FunSuite with TestHelpers {
  import InoxConvertible._
  import StringConcatExtended._
  import core.predef.AssociativeInsert

  implicit def tupleToTupleExpr[A: InoxConvertible, B: InoxConvertible](in: (A, B)): (Expr, Expr) = {
    (in._1: Expr, in._2: Expr)
  }
  implicit def tupleToTupleExpr[A: InoxConvertible](in: (A, Expr)): (Expr, Expr) = {
    (in._1: Expr, in._2: Expr)
  }

  test("Revert the use of a map") {
    val pfun =
      let("tr" :: TMap[String, String],
        _Map[String, String](
          "hello" -> "Bonjour",
          "howareu" -> "comment tu vas?",
          "useless1" -> "useless1",
          "useless2" -> "useless2",
          "useless3" -> "useless3"
        )
      ){ trv =>
        MapApply(trv, "hello") +& ", "  +& MapApply(trv, "howareu")
      }

    checkProg("Bonjour, comment tu vas?", pfun)
    val pfun2 = repairProgram(pfun, "Salut, comment tu vas?")
    checkProg("Salut, comment tu vas?", pfun2) match {
      case Let(t, FiniteMap(pairs, default, _, _), MapApply(t2, StringLiteral("hello")) +& StringLiteral(", ") +& MapApply(t3, StringLiteral("howareu"))) =>
        pairs.toList shouldEqual List[(Expr, Expr)](
          "hello" -> "Salut",
          "howareu" -> "comment tu vas?",
          "useless1" -> "useless1",
          "useless2" -> "useless2",
          "useless3" -> "useless3")
    }
  }

  test("Revert the use of a double variable and a map") {
    val pfun = 
      let("firstname" :: String, "Mikael"){ firstname =>
      let("tr" :: TMap[String, String],
        _Map[String, String](
          "hello" -> ("Bonjour " +& firstname),
          "howareu" -> (", comment tu vas, " +& firstname),
          "useless1" -> "useless1",
          "useless2" -> "useless2",
          "useless3" -> "useless3"
        )
      ){ trv => MapApply(trv, "hello") +& MapApply(trv, "howareu") }  }

    checkProg("Bonjour Mikael, comment tu vas, Mikael", pfun)

    checkProg("Bonjour Ravi, comment tu vas, Ravi",
      repairProgram(pfun, StringInsert("Bonjour ", "Ravi", ", comment tu vas, Mikael", AssociativeInsert.InsertAutomatic))) match {
      case Let(firstNameVal, StringLiteral(name), Let(_, FiniteMap(pairs, default, _, _), _)) =>
        name shouldEqual "Ravi"
        val fv = firstNameVal.toVariable
        pairs.toList shouldEqual List[(Expr, Expr)](
          "hello" -> ("Bonjour " +& fv),
          "howareu" -> (", comment tu vas, " +& fv),
          "useless1" -> "useless1",
          "useless2" -> "useless2",
          "useless3" -> "useless3"
        )
    }

    checkProg("Bonjour Ravi, comment tu vas, Ravi",
    repairProgram(pfun, "Bonjour Ravi, comment tu vas, Mikael")) match {
      case Let(firstNameVal, StringLiteral(name), Let(_, FiniteMap(pairs, default, _, _), _)) =>
        name shouldEqual "Ravi"
        val fv = firstNameVal.toVariable
        pairs.toList shouldEqual List[(Expr, Expr)](
        "hello" -> ("Bonjour " +& fv),
        "howareu" -> (", comment tu vas, " +& fv),
        "useless1" -> "useless1",
        "useless2" -> "useless2",
        "useless3" -> "useless3"
        )
    }
  }

  test("Repair non-existent values") {
    val pfun = 
      let("tr" :: TMap[String, String],
        _Map[String, String](
          "hello" -> ("Hello " +& "World"),
          "howareu" -> (", comment tu vas" +& "???")
        )
      ){ trv => MapApply(trv, "newkey") }


    checkProg(Utils.defaultValue(String)(Utils.defaultSymbols), pfun)
    checkProg("New world",
      repairProgram(pfun, "New world")) match {
      case Let(tr, FiniteMap(pairs, _, _, _), MapApply(_, StringLiteral("newkey"))) =>
        pairs should contain((StringLiteral("newkey"), StringLiteral("New world")))
        pairs should contain((StringLiteral("hello"), "Hello " +& "World"))
        pairs should contain((StringLiteral("howareu"), ", comment tu vas" +& "???"))
    }
  }

  test("Repair double map indirection") {
    val pfun =
      let("lang" :: StringType, "fr")(lang =>
        let("tr" :: TMap[String, Map[String, String]],
          _Map[String, Map[String, String]](
            "fr" -> _Map[String, String]("hello" -> "Bonjour"),
            "en" -> _Map[String, String]("hello" -> "Hello")
          )
        ){ trv =>
          MapApply(MapApply(trv, lang), "hello") +& " " +& lang
        }
      )
    implicit val v = Utils.defaultSymbols

    checkProg("Hello en",
      repairProgram(pfun, "Bonjour en"))

    checkProg("Bonjour fr", pfun)
    checkProg("Salut fr",
      repairProgram(pfun, "Salut fr")) match {
      case Let(lang, StringLiteral(l), Let(tr, m, MapApply(MapApply(_, langVar1), StringLiteral("hello")) +& StringLiteral(" ") +& langVar2)) =>
        l shouldEqual "fr"
        langVar1 shouldEqual lang.toVariable
        langVar2 shouldEqual langVar1

        m shouldEqual
        FiniteMap(
          Seq(
            (StringLiteral("fr"), FiniteMap(
              Seq((StringLiteral("hello"), StringLiteral("Salut"))),
              Utils.defaultValue(String), StringType, StringType
            )), (StringLiteral("en"), FiniteMap(
              Seq((StringLiteral("hello"), StringLiteral("Hello"))),
              Utils.defaultValue(String), StringType, StringType
            ))), Utils.defaultValue(TMap[String, String]), StringType, TMap[String, String])
    }
  }
  // TODO: Revert MapUpdated.

  test("Revert the use of a bag") {

  }

  test("Revert SetAdd") {
    val pfun =
      let("flags" :: TSet[String],
        _Set[String]("cvc4", "z3")
      ){ flags =>
        let("oflags" :: String, "debug"){ oflags =>
          SetAdd(flags, oflags)
        }
      }

    pfun shouldProduce _Set[String]("cvc4", "debug",  "z3")
    pfun repairFrom _Set[String]("cvc4", "debug", "z3", "vampire") shouldProduce
      _Set[String]("cvc4", "debug",  "vampire", "z3")
  }
}
