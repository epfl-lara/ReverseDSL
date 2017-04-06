package perfect
import inox._
import inox.trees._
import inox.trees.dsl._
import org.scalatest._
import matchers._
import Matchers.{=== => _, _}
import perfect.InoxConvertible.{_List, inoxTypeOf, valdef}
import perfect.ReverseProgram.ProgramFormula

/**
  * Created by Mikael on 01/04/2017.
  */
class BenchmarksTest extends FunSuite with TestHelpers {
  import StringConcatExtended._

  test("Small translation") {
    val init_translations = FiniteMap(
      Seq(StringLiteral("en") ->
        FiniteMap(
          Seq(StringLiteral("hello") -> StringLiteral("Hi"),
            StringLiteral("howareu") -> StringLiteral(", how are you doing?")
          ),
          StringLiteral("..."),
          StringType, StringType
        ),
        StringLiteral("fr") ->
          FiniteMap(
            Seq(StringLiteral("hello") -> StringLiteral("Salut"),
              StringLiteral("howareu") -> StringLiteral(", comment tu vas ?")
            ),
            StringLiteral("..."),
            StringType, StringType
          )),
      FiniteMap(Seq(), StringLiteral("..."), StringType, StringType),
      StringType,
      inoxTypeOf[Map[String, String]]
    )

    var pfun: Expr =
      let("name"::StringType, StringLiteral("Marion"))(name =>
        let("language"::StringType, StringLiteral("en"))(language =>
          let("translations"::inoxTypeOf[Map[String, Map[String, String]]], init_translations)(translations =>
            let("tr"::inoxTypeOf[Map[String, String]], MapApply(translations, language))(tr =>
              //StringLiteral("(") +& language +& StringLiteral(")\n") +&
                MapApply(tr, StringLiteral("hello")) +& StringLiteral(" ") +& name
            )
          )
        )
      )

    pfun shouldProduce "Hi Marion"

    pfun repairFrom ProgramFormula.StringInsert("","G"," Marion") shouldProduce "G Marion"
  }


  /*test("Big translation") {
    val init_translations = FiniteMap(
      Seq(StringLiteral("en") ->
        FiniteMap(
          Seq(StringLiteral("hello") -> StringLiteral("Hi"),
            StringLiteral("howareu") -> StringLiteral(", how are you doing?")
          ),
          StringLiteral("..."),
          StringType, StringType
        ),
        StringLiteral("fr") ->
          FiniteMap(
            Seq(StringLiteral("hello") -> StringLiteral("Salut"),
              StringLiteral("howareu") -> StringLiteral(", comment tu vas ?")
            ),
            StringLiteral("..."),
            StringType, StringType
          )),
      FiniteMap(Seq(), StringLiteral("..."), StringType, StringType),
      StringType,
      inoxTypeOf[Map[String, String]]
    )

    val init_list = _List[String](
      StringLiteral("Margharita"),
      StringLiteral("Salami"),
      StringLiteral("Pepperoni"),
      StringLiteral("Ham")
    )

    var pfun: Expr = {
      val l = valdef[String]("l")
      let("name"::StringType, StringLiteral("Marion"))(name =>
        let("language"::StringType, StringLiteral("en"))(language =>
          let("translations"::inoxTypeOf[Map[String, Map[String, String]]], init_translations)(translations =>
            let("tr"::inoxTypeOf[Map[String, String]], MapApply(translations, language))(tr =>
              StringLiteral("(") +& language +& StringLiteral(")\n") +&
                MapApply(tr, StringLiteral("hello")) +& StringLiteral(" ") +& name +&
                MapApply(tr, StringLiteral("howareu")) +& StringLiteral("\n\n") +& name +& StringLiteral(", here are the available pizzas:\n") +&
                E(Utils.mkString)()(
                  E(Utils.map)(String, String)(init_list, \("l"::String)(l => StringLiteral("- ") +& l)),
                  StringLiteral("\n")
                )
            )
          )
        )
      )
    }

    pfun shouldProduce "(en)\nHi Marion, how are you doing?\n\nMarion, here are the available pizzas:\n- Margharita\n- Salami\n- Pepperoni\n- Ham"

    pfun repairFrom ProgramFormula.StringInsert("(en)\n","G"," Marion, how are you doing?\n\nMarion, here are the available pizzas:\n- Margharita\n- Salami\n- Pepperoni\n- Ham") shouldProduce
      "(en)\nG Marion, how are you doing?\n\nMarion, here are the available pizzas:\n- Margharita\n- Salami\n- Pepperoni\n- Ham"

    pfun repairFrom ProgramFormula.StringInsert("(en)\nHi Marion, how are you doing?\n\nMarion, here are the available pizzas:\n- Margharita\n- Salami","s","\n- Pepperoni\n- Ham") shouldProduce
      "(en)\nHi Marion, how are you doing?\n\nMarion, here are the available pizzas:\n- Margharita\n- Salamis\n- Pepperoni\n- Ham"

    pfun repairFrom ProgramFormula.StringInsert("(en)\nHi Marion, how are you doing?\n\nMarion, here are the available pizzas:\n- Margharita\n- ","B","Salami\n- Pepperoni\n- Ham") shouldProduce
      "(en)\nHi Marion, how are you doing?\n\nMarion, here are the available pizzas:\n- Margharita\n- BSalami\n- Pepperoni\n- Ham"

    pfun repairFrom ProgramFormula.StringInsert("(en)\nHi Marion, how are you doing?\n\nMarion, here are the available pizzas:\n- Margharita\n","*"," Salami\n- Pepperoni\n- Ham") shouldProduce
      "(en)\nHi Marion, how are you doing?\n\nMarion, here are the available pizzas:\n* Margharita\n* Salami\n* Pepperoni\n* Ham"

    pfun repairFrom ProgramFormula.StringInsert("(en)\nHi Marion, how are you doing?\n\nMarion, here are the available pizzas:\n- Margharita\n-"," "," Salami\n- Pepperoni\n- Ham") shouldProduce
      "(en)\nHi Marion, how are you doing?\n\nMarion, here are the available pizzas:\n-  Margharita\n-  Salami\n-  Pepperoni\n-  Ham"

    pfun repairFrom ProgramFormula.StringInsert("(","fr",")\nHi Marion, how are you doing?\n\nMarion, here are the available pizzas:\n- Margharita\n- Salami\n- Pepperoni\n- Ham") shouldProduce
      "(fr)\nSalut Marion, comment tu vas ?\n\nMarion, here are the available pizzas:\n- Margharita\n- Salami\n- Pepperoni\n- Ham"
  }*/

  val text = """# Proof by induction
    |A proof by induction uses the axiom of recurrence.
    |The axiom of recurrence states that if the following precondition is satisfied:
    |
    |    $P(1) \wedge \forall n \ge 1. P(n) => P(n+1)$
    |
    |then the following result holds:
    |
    |    $\forall n \ge 1. P(n)$
    |
    |If we want to prove a proposition $P(n)$ for any $n$, we first need to prove that $P(1)$ holds, and that if we know $P(n)$, we can obtain $P(n+1)$.
    |
    |A simple application of proof by induction is to prove that the sum of numbers between 1 and n is equal to $n(n+1)/2$.
    |This can be conjectured: the sum of numbers between 1 and 3 is 1+2+3 = 6. On the other side 3*(3+1)/2 = 12/2 = 6. Hence $P(3)$ holds.
    |
    |By applying proof by induction, this result is trivially true for $1$. Now suppose that it is true for a given $n$. $1+\ldots+n = n(n+1)/2$. Adding $n+1$ to both sides gives: $1+\ldots+n+(n+1) = n(n+1)/2 + n+1 = (n+1)(n+2)/2$. Hence we can conclude.
    |
    |There are many variants of proof by induction: induction basis equal to 2, prefix induction, induction on multiple counters, infinite descent
    |""".stripMargin

  test("Perfect demo") {

  }
}
