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
        StringConcat(StringConcat(MapApply(trv, "hello"), ", "), MapApply(trv, "howareu"))
      }
    )(inoxTypeOf[String])

    checkProg("Bonjour, comment tu vas?", pfun)
    checkProg("Salut, comment tu vas?", repairProgram(pfun, "Salut, comment tu vas?")) matchBody {
      case Let(t, m, StringConcat(
          StringConcat(MapApply(t2, StringLiteral("hello")), StringLiteral(", ")), MapApply(t3, StringLiteral("howareu")))) =>
        exprOfInox[Map[String, String]](m) shouldEqual Map("hello" -> "Salut", "howareu" -> "comment tu vas?")
    }
  }

  test("Revert the use of a double map") {
    val pfun = function(
      let("firstname" :: inoxTypeOf[String], "Mikael"){ firstname =>
      let("tr" :: inoxTypeOf[Map[String, String]],
        _Map[String, String](
          "hello" -> StringConcat("Bonjour ", firstname),
          "howareu" -> StringConcat(", comment tu vas, ", firstname)
        )
      ){ trv =>
        StringConcat(MapApply(trv, "hello"), MapApply(trv, "howareu"))
      }
      }
    )(inoxTypeOf[String])

    checkProg("Bonjour Mikael, comment tu vas, Mikael", pfun)
    checkProg("Bonjour Ravi, comment tu vas, Ravi",
      repairProgram(pfun, "Bonjour Ravi, comment tu vas, Mikael"))
  }

  test("Revert the use of a bag") {

  }

  test("Revert the use of a set") {

  }
}
