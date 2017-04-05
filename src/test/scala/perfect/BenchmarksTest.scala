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

    var program: Expr = {
      val l = valdef[String]("l")
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
    }
    val pfun = function(
      program
    )(inoxTypeOf[String])
    pfun shouldProduce "Hi Marion"

    pfun repairFrom ProgramFormula.StringInsert("","G"," Marion") shouldProduce "G Marion"
  }


  test("Big translation") {
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

    var program: Expr = {
      val l = valdef[String]("l")
      let("name"::StringType, StringLiteral("Marion"))(name =>
        let("language"::StringType, StringLiteral("en"))(language =>
          let("translations"::inoxTypeOf[Map[String, Map[String, String]]], init_translations)(translations =>
            let("tr"::inoxTypeOf[Map[String, String]], MapApply(translations, language))(tr =>
              StringLiteral("(") +& language +& StringLiteral(")\n") +&
                MapApply(tr, StringLiteral("hello")) +& StringLiteral(" ") +& name +&
                MapApply(tr, StringLiteral("howareu")) +& StringLiteral("\n\n") +& name +& StringLiteral(", here are the available pizzas:\n") +&
                FunctionInvocation(
                  Utils.mkString,
                  Seq(),
                  Seq(
                    FunctionInvocation(Utils.map, Seq(StringType, StringType),
                      Seq(init_list, Lambda(
                        Seq(l), StringLiteral("- ") +& l.toVariable
                      ))),
                    StringLiteral("\n")
                  )
                )
            )
          )
        )
      )
    }
    val pfun = function(
      program
    )(inoxTypeOf[String])
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
  }
}
