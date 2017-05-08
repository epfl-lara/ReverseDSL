package perfect
import inox._
import inox.trees.{not => dnot, _}
import inox.trees.dsl._
import org.scalatest._
import matchers._
import Matchers.{=== => _, _}
import perfect.ProgramFormula.CloneTextMultiple

/**
  * Created by Mikael on 08/05/2017.
  */
class FormulaTest extends FunSuite with TestHelpers {
  import InoxConvertible._
  import ImplicitTuples._

  implicit val symbols = Utils.defaultSymbols
  test("combineWith") {
    val a = variable[(String, String)]("a")
    val x0 = variable[String]("x0")
    val x1 = variable[String]("x1")
    val x2 = variable[String]("x2")
    val x3 = variable[String]("x3")
    val formula1 = Formula(Map(a -> StrongValue(ADT(ADTType(tuple2, Seq(String, String)), Seq(x0, x1))),
      x0 -> StrongValue("B1"),
      x1 -> OriginalValue("A2")
    ))
    val formula2 = Formula(Map(a -> StrongValue(ADT(ADTType(tuple2, Seq(String, String)), Seq(x2, x3))),
      x2 -> OriginalValue("A1"),
      x3 -> StrongValue("B2")
    ))
    val res = formula1 combineWith formula2
    res.constraints shouldEqual BooleanLiteral(true)

    res.known.size shouldEqual 5
  }

}
