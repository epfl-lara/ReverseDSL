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

  test("Revert the use of a map") {
    /*val build = Variable(FreshIdentifier("m"), FunctionType(Seq(inoxTypeOf[String]), inoxTypeOf[Element]), Set())
    val v = variable[String]("v")
    val vText = variable[String]("text")*/
    val tr = valdef[Map[String, String]]("tr")
    val translations = _Map[String, String](
      "hello" -> "Bonjour",
      "howareu" -> "comment tu vas?"
    )
    val pfun = function(
      let(tr, translations){ trv =>
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
    /*val build = Variable(FreshIdentifier("m"), FunctionType(Seq(inoxTypeOf[String]), inoxTypeOf[Element]), Set())
    val v = variable[String]("v")
    val vText = variable[String]("text")*/
    //val translations =
  }

  test("Revert the use of a bag") {

  }

  test("Revert the use of a set") {

  }
}
