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

/**
  * Created by Mikael on 22/03/2017.
  */
class BagMapSetTest extends FunSuite with TestHelpers {
  import InoxConvertible._
  import StringConcatExtended._

  implicit def tupleToTupleExpr[A: InoxConvertible, B: InoxConvertible](in: (A, B)): (Expr, Expr) = {
    (in._1: Expr, in._2: Expr)
  }
  implicit def tupleToTupleExpr[A: InoxConvertible](in: (A, Expr)): (Expr, Expr) = {
    (in._1: Expr, in._2: Expr)
  }

  test("Revert the use of a map") {
    val pfun = function(
      let("tr" :: inoxTypeOf[Map[String, String]],
        _Map[String, String](
          "hello" -> "Bonjour",
          "howareu" -> "comment tu vas?"
        )
      ){ trv =>
        MapApply(trv, "hello") +& ", "  +& MapApply(trv, "howareu")
      }
    )(inoxTypeOf[String])

    checkProg("Bonjour, comment tu vas?", pfun)
    checkProg("Salut, comment tu vas?", repairProgram(pfun, "Salut, comment tu vas?")) matchBody {
      case Let(t, m, MapApply(t2, StringLiteral("hello")) +& StringLiteral(", ") +& MapApply(t3, StringLiteral("howareu"))) =>
        exprOfInox[Map[String, String]](m) shouldEqual Map("hello" -> "Salut", "howareu" -> "comment tu vas?")
    }
  }

  test("Revert the use of a double variable and a map") {
    val pfun = function(
      let("firstname" :: inoxTypeOf[String], "Mikael"){ firstname =>
      let("tr" :: inoxTypeOf[Map[String, String]],
        _Map[String, String](
          "hello" -> ("Bonjour " +& firstname),
          "howareu" -> (", comment tu vas, " +& firstname)
        )
      ){ trv => MapApply(trv, "hello") +& MapApply(trv, "howareu") }  }
    )(inoxTypeOf[String])

    checkProg("Bonjour Mikael, comment tu vas, Mikael", pfun)
    checkProg("Bonjour Ravi, comment tu vas, Ravi",
      repairProgram(pfun, "Bonjour Ravi, comment tu vas, Mikael"))
  }

  test("Repair non-existent values") {
    val pfun = function(
      let("tr" :: inoxTypeOf[Map[String, String]],
        _Map[String, String](
          "hello" -> ("Hello " +& "World"),
          "howareu" -> (", comment tu vas" +& "???")
        )
      ){ trv => MapApply(trv, "newkey") }
    )(inoxTypeOf[String])

    checkProg(Utils.defaultValue(inoxTypeOf[String])(Utils.defaultSymbols), pfun)
    checkProg("New world",
      repairProgram(pfun, "New world")) matchBody {
      case Let(tr, FiniteMap(pairs, _, _, _), MapApply(_, StringLiteral("newkey"))) =>
        pairs should contain((StringLiteral("newkey"), StringLiteral("New world")))
        pairs should contain((StringLiteral("hello"), "Hello " +& "World"))
        pairs should contain((StringLiteral("howareu"), ", comment tu vas" +& "???"))
    }
  }

  test("Repair double map indirection") {
    val pfun = function(
      let("tr" :: inoxTypeOf[Map[String, Map[String, String]]],
        _Map[String, Map[String, String]](
          "fr" -> _Map[String, String]("hello" -> "Bonjour"),
          "en" -> _Map[String, String]("hello" -> "Hello")
        )
      ){ trv =>
        MapApply(MapApply(trv, "fr"), "hello")
      }
    )(inoxTypeOf[String])

    checkProg("Bonjour", pfun)
    checkProg("Salut",
      repairProgram(pfun, "Salut")) matchBody {
      case Let(tr, FiniteMap(
        Seq(
        (StringLiteral("fr"), FiniteMap(
          Seq((StringLiteral("hello"), StringLiteral(hellofr))),
          _, _, _
        )), (StringLiteral("en"), FiniteMap(
        Seq((StringLiteral("hello"), StringLiteral(helloen))),
        _, _, _
        ))), _, _, _), MapApply(MapApply(_, StringLiteral("fr")), StringLiteral("hello"))) =>
        hellofr shouldEqual "Salut"
        helloen shouldEqual "Hello"
    }
  }
  // TODO: Revert MapUpdated.

  test("Revert the use of a bag") {

  }

  test("Revert SetAdd") {
    val pfun = function(
      let("flags" :: inoxTypeOf[Set[String]],
        _Set[String](
          "cvc4", "z3"
        )
      ){ flags =>
        let("oflags" :: inoxTypeOf[String],
          "debug"
        ){ oflags =>
          SetAdd(flags, oflags)
        }
      }
    )(inoxTypeOf[Set[String]])

    checkProg(_Set[String]("cvc4", "debug",  "z3"), pfun)
    checkProg(_Set[String]("cvc4", "debug",  "vampire", "z3"),
      repairProgram(pfun, _Set[String]("cvc4", "debug", "z3", "vampire")))
  }
}
