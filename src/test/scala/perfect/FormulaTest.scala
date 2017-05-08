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
  test("combineWith merges ADT") {
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

  test("combineWith does it best to avoid constraints") {
    val a = variable[String]("a")
    val b = variable[String]("b")
    val c = variable[String]("c")
    val d = variable[String]("d")

    val formula1 = Formula(Map(a -> OriginalValue(" "),
      b -> StrongValue(a)
    ))
    val formula2 = Formula(Map(c -> OriginalValue(" "),
      b -> StrongValue(c)
    ))
    val formula = formula1 combineWith formula2
    formula.constraints shouldEqual BooleanLiteral(true)
  }

  test("Propagate constraints up to the original value") {
    val a = variable[String]("a")
    val b = variable[String]("b")
    val c = variable[String]("c")
    val d = variable[String]("d")

    val formula1 = Formula(Map(a -> StrongValue(b), b -> StrongValue(c), c -> StrongValue(d), d -> OriginalValue(" ")))
    val formula2 = Formula(Map(a -> StrongValue("A")))

    val formula = formula1 combineWith formula2

    formula.known(d) shouldEqual StrongValue("A")
  }

  test("Combining with a tautology") {
    val a = variable[String]("a")
    val b = variable[String]("b")
    val c = variable[String]("c")
    val d = variable[String]("d")

    val formula1 = Formula(Map(a -> StrongValue(b), b -> StrongValue(c), c -> StrongValue(d), d -> StrongValue(" ")))
    val formula2 = Formula(Map(a -> StrongValue(c)))

    (formula1 combineWith formula2) shouldEqual formula1

  }

  test("Combining with a tautology inverted") {
    val a = variable[String]("a")
    val b = variable[String]("b")
    val c = variable[String]("c")
    val d = variable[String]("d")

    val formula1 = Formula(Map(a -> StrongValue(b), b -> StrongValue(c), c -> StrongValue(d), d -> StrongValue(" ")))
    val formula2 = Formula(Map(c -> StrongValue(a)))

    (formula1 combineWith formula2) shouldEqual formula1
  }

  test("Avoid circularities") {
    val a = variable[String]("a")
    val b = variable[String]("b")
    val c = variable[String]("c")
    val d = variable[String]("d")

    val formula1 = Formula(Map(a -> StrongValue(b)))
    val formula2 = Formula(Map(c -> OriginalValue("it "), b->StrongValue(c), a -> StrongValue("at ")))
    val formulaT = Formula(Map(c -> StrongValue("at "), b->StrongValue(c), a -> StrongValue(b)))

    formula1 combineWith formula2 shouldEqual formulaT
  }

  test("Avoid circularities 2") {
    val a = variable[String]("a")
    val b = variable[String]("b")
    val c = variable[String]("c")
    val d = variable[String]("d")

    val formula1 = Formula(Map(b -> StrongValue("B"), a-> StrongValue(c), c->StrongValue("B")))
    val formula2 = Formula(Map(b -> StrongValue(a)))

    formula1 combineWith formula2 shouldEqual formula1
  }
  
  test("Propagate combineWith") {
    val a = variable[String]("a")
    val b = variable[String]("b")
    val c = variable[String]("c")

    val formula1 = Formula(Map(
    c->OriginalValue("it "),
    a->StrongValue(c),
    b->StrongValue("at ")))
    val formula2 = Formula(Map(
    b -> StrongValue(a)))

    val formula = Log activated (formula1 combineWith formula2)
    formula.constraints shouldEqual BooleanLiteral(true)
  }

  test("Propagate combineWith more complex") {
    val a = variable[String]("a")
    val b = variable[String]("b")
    val c = variable[String]("c")
    val d = variable[String]("d")

    val formula1 = Formula(Map(
      c->OriginalValue("it "),
      a->StrongValue(c), d -> StrongValue(b),
      b->StrongValue("at ")))
    val formula2 = Formula(Map(
      d -> StrongValue(a)))

    val formula = formula1 combineWith formula2
    formula.constraints shouldEqual BooleanLiteral(true)
  }

  test("Avoid same predicates") {
    val a = variable[String]("a")
    val b = variable[String]("b")
    val c = variable[String]("c")

    val formula1 = Formula(Map(a -> StrongValue(b), b -> OriginalValue("C")))
    val formula2 = Formula(Map(a -> StrongValue(b)))

    Log activated (
    formula1 combineWith formula2 shouldEqual formula1)
  }
}
