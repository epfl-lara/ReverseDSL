package perfect
import inox._
import inox.trees._
import inox.trees.dsl._
import org.scalatest._
import matchers._
import Matchers.{=== => _, _}
import perfect.InoxConvertible.{_List, inoxTypeOf, valdef}

/**
  * Created by Mikael on 01/04/2017.
  */
class BenchmarksTest extends FunSuite with TestHelpers {/*
  import StringConcatExtended._
  import InoxConvertible._
  import ImplicitTuples._
  import ProgramFormula._

  val step1: Expr = """# Proof by induction
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

  test("Perfect demo step2 (clone to variable p)") {
    val step2 = step1 repairFrom
      ProgramFormula.CloneText("""# Proof by induction
     |A proof by induction uses the axiom of recurrence.
     |The axiom of recurrence states that if the following precondition is satisfied:
     |
     |    $""".stripMargin, "P", """(1) \wedge \forall n \ge 1. P(n) => P(n+1)$
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
     |""".stripMargin)
    step2 shouldProduce step1
    step2 match {
      case Let(v, StringLiteral(s), body) =>
        v.id.name shouldEqual "p"
        s shouldEqual "P"
        if(!isVarIn(v.id, body)) fail(s"The variable $v was not used in $body")
    }
  }

  test("Perfect demo step2-1 (paste of variable p)") {
    val step2 = let("p"::String, "P")(p =>
      """# Proof by induction
      |A proof by induction uses the axiom of recurrence.
      |The axiom of recurrence states that if the following precondition is satisfied:
      |
      |    $""" +& p +& """(1) \wedge \forall n \ge 1. P(n) => P(n+1)$
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
    )
    val v = step2.vd.toVariable

    val step3 = step2 repairFrom
      ProgramFormula.PasteVariable("""# Proof by induction
      |A proof by induction uses the axiom of recurrence.
      |The axiom of recurrence states that if the following precondition is satisfied:
      |
      |    $P(1) \wedge \forall n \ge 1. """.stripMargin, v, "P", """(n) => P(n+1)$
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
      |""".stripMargin, ProgramFormula.PasteVariable.PasteAutomatic)

    step3 shouldProduce step1

    step3 match {
      case Let(v, StringLiteral(s), body) =>
        s shouldEqual "P"
        if(countVarIn(v.id, body) != 2) fail(s"The variable $v was not used exactly twice in $body")
    }
  }

  test("Perfect demo step2-2 (change of variable p from text)") {
    val step2 = let("p"::String, "P")(p =>
      """# Proof by induction
      |A proof by induction uses the axiom of recurrence.
      |The axiom of recurrence states that if the following precondition is satisfied:
      |
      |    $""".stripMargin +& p +& """(1) \wedge \forall n \ge 1. """ +& p +& """(n) => """ +& p +& """(n+1)$
      |
      |then the following result holds:
      |
      |    $\forall n \ge 1. """.stripMargin +& p +& """(n)$
      |
      |If we want to prove a proposition $""".stripMargin +& p +& """(n)$ for any $n$, we first need to prove that $""" +& p +& """(1)$ holds, and that if we know $""" +& p +& """(n)$, we can obtain $""" +& p +& """(n+1)$.
      |
      |A simple application of proof by induction is to prove that the sum of numbers between 1 and n is equal to $n(n+1)/2$.
      |This can be conjectured: the sum of numbers between 1 and 3 is 1+2+3 = 6. On the other side 3*(3+1)/2 = 12/2 = 6. Hence $""".stripMargin +& p +& """(3)$ holds.
      |
      |By applying proof by induction, this result is trivially true for $1$. Now suppose that it is true for a given $n$. $1+\ldots+n = n(n+1)/2$. Adding $n+1$ to both sides gives: $1+\ldots+n+(n+1) = n(n+1)/2 + n+1 = (n+1)(n+2)/2$. Hence we can conclude.
      |
      |There are many variants of proof by induction: induction basis equal to 2, prefix induction, induction on multiple counters, infinite descent
      |""".stripMargin
    )
    val v = step2.vd.toVariable

    val step3 = step2 repairFrom
      StringInsert("""# Proof by induction
      |A proof by induction uses the axiom of recurrence.
      |The axiom of recurrence states that if the following precondition is satisfied:
      |
      |    $P(1) \wedge \forall n \ge 1. """.stripMargin, "H", """(n) => P(n+1)$
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
      |""".stripMargin, StringInsert.InsertAutomatic)

    step3 match {
      case Let(v, StringLiteral(s), body) =>
        s shouldEqual "H"
        if(countVarIn(v.id, body) != 9) fail(s"The variable $v was not used exactly 9 times in $body")
    }
  }

  test("Perfect demo step3 (change of variable n from text)") {
    val step2 = let("p"::String, "P")(p =>
      """# Proof by induction
      |A proof by induction uses the axiom of recurrence.
      |The axiom of recurrence states that if the following precondition is satisfied:
      |
      |    $""".stripMargin +& p +& """(1) \wedge \forall n \ge 1. """ +& p +& """(n) => """ +& p +& """(n+1)$
      |
      |then the following result holds:
      |
      |    $\forall n \ge 1. """.stripMargin +& p +& """(n)$
      |
      |If we want to prove a proposition $""".stripMargin +& p +& """(n)$ for any $n$, we first need to prove that $""" +& p +& """(1)$ holds, and that if we know $""" +& p +& """(n)$, we can obtain $""" +& p +& """(n+1)$.
      |
      |A simple application of proof by induction is to prove that the sum of numbers between 1 and n is equal to $n(n+1)/2$.
      |This can be conjectured: the sum of numbers between 1 and 3 is 1+2+3 = 6. On the other side 3*(3+1)/2 = 12/2 = 6. Hence $""".stripMargin +& p +& """(3)$ holds.
      |
      |By applying proof by induction, this result is trivially true for $1$. Now suppose that it is true for a given $n$. $1+\ldots+n = n(n+1)/2$. Adding $n+1$ to both sides gives: $1+\ldots+n+(n+1) = n(n+1)/2 + n+1 = (n+1)(n+2)/2$. Hence we can conclude.
      |
      |There are many variants of proof by induction: induction basis equal to 2, prefix induction, induction on multiple counters, infinite descent
      |""".stripMargin    )
    val v = step2.vd.toVariable

    val step3 = step2 repairFrom
      ProgramFormula.CloneText("""# Proof by induction
      |A proof by induction uses the axiom of recurrence.
      |The axiom of recurrence states that if the following precondition is satisfied:
      |
      |    $P(1) \wedge \forall """.stripMargin, "n", """ \ge 1. P(n) => P(n+1)$
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
      |""".stripMargin)

    val newValDef = step3 match {
      case Let(p, StringLiteral(ps), Let(n, StringLiteral(ns), body)) =>
        ps shouldEqual "P"
        ns shouldEqual "n"
        if(countVarIn(p.id, body) != 9) fail(s"The variable $p was not used exactly 9 times in $body")
        if(countVarIn(n.id, body) != 1) fail(s"The variable $n did not appear in $body")
        n
    }
    
    val step31 = step3 repairFrom ProgramFormula.PasteVariable("""# Proof by induction
      |A proof by induction uses the axiom of recurrence.
      |The axiom of recurrence states that if the following precondition is satisfied:
      |
      |    $P(1) \wedge \forall n \ge 1. P(""".stripMargin, newValDef.toVariable, "n", """) => P(n+1)$
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
      |""".stripMargin, ProgramFormula.PasteVariable.PasteAutomatic)

    step31 match {
      case Let(p, StringLiteral(ps), Let(n, StringLiteral(ns), body)) =>
        ps shouldEqual "P"
        ns shouldEqual "n"
        if(countVarIn(p.id, body) != 9) fail(s"The variable $p was not used exactly 9 times in $body")
        if(countVarIn(n.id, body) != 2) fail(s"The variable $n did not appear twice in $body")
        n
    }
  }

  test("Perfect demo step4 (change of the constant 1)") {
    // Just to remember the step.
  }

  test("Perfect demo step5 (translate Proof By Induction)") {
    
  }


  test("Perfect demo step8 (change of the title to French)") {
    val step7 =
      let("language"::String, "fr")(language =>
      let("d"::inoxTypeOf[String => (String, String)], \("a"::String)(a => _Tuple2(String, String)(a, a)))(d =>
      let("tDefault"::inoxTypeOf[Map[String, (String, String)]], _Map[String, (String, String)](("title": Expr) -> Application(d, Seq("Proof by induction"))))(tDefault =>
      let("translations"::inoxTypeOf[Map[String, Map[String, (String, String)]]],
        _MapWithDefault[String, Map[String, (String, String)]](tDefault, ("en": Expr) -> tDefault, ("fr": Expr) -> _Map[String, (String, String)](
          ("title": Expr) -> _Tuple2(String, String)("Proof by induction", "Proof by induction")
        ))
      )( translations =>
      let("t"::inoxTypeOf[String => String], \("key"::String)(key => MapApply(MapApply(translations, language), key).getField(_1)))(t =>
        let("p"::String, "P")(p =>
          """# """ +& Application(t, Seq("title")) +& """
      |A proof by induction uses the axiom of recurrence.
      |The axiom of recurrence states that if the following precondition is satisfied:
      |
      |    $""".stripMargin +& p +& """(1) \wedge \forall n \ge 1. """ +& p +& """(n) => """ +& p +& """(n+1)$
      |
      |then the following result holds:
      |
      |    $\forall n \ge 1. """.stripMargin +& p +& """(n)$
      |
      |If we want to prove a proposition $""".stripMargin +& p +& """(n)$ for any $n$, we first need to prove that $""" +& p +& """(1)$ holds, and that if we know $""" +& p +& """(n)$, we can obtain $""" +& p +& """(n+1)$.
      |
      |A simple application of proof by induction is to prove that the sum of numbers between 1 and n is equal to $n(n+1)/2$.
      |This can be conjectured: the sum of numbers between 1 and 3 is 1+2+3 = 6. On the other side 3*(3+1)/2 = 12/2 = 6. Hence $""".stripMargin +& p +& """(3)$ holds.
      |
      |By applying proof by induction, this result is trivially true for $1$. Now suppose that it is true for a given $n$. $1+\ldots+n = n(n+1)/2$. Adding $n+1$ to both sides gives: $1+\ldots+n+(n+1) = n(n+1)/2 + n+1 = (n+1)(n+2)/2$. Hence we can conclude.
      |
      |There are many variants of proof by induction: induction basis equal to 2, prefix induction, induction on multiple counters, infinite descent
      |""".stripMargin
      )
      )
      )
      )
      )
      )
    
    // Replace selection by "P", and then later insert.
    
    val step81 = step7 repairFrom StringInsert("""# """.stripMargin, "P", """
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
      |""".stripMargin, StringInsert.InsertAutomatic
    )

    val step82 = step81 repairFrom StringInsert("""# P""".stripMargin, "reuve par recurrence", """
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
      |""".stripMargin, StringInsert.InsertAutomatic
    )

    step82 match {
      case Let(language, _, Let(d, _, Let(tDefault, _, Let(translations, fm@FiniteMap(pairs, _ ,_ , _), _)))) =>
        val frMap = pairs.collectFirst {
          case (k, v: FiniteMap) if k == StringLiteral("fr") => v
        }.getOrElse(fail(s"Could not find fr map in $fm"))
         frMap.pairs.collectFirst {
        case (k, ADT(ADTType(`tuple2`, _), Seq(prev, next))) if k == StringLiteral("title") =>
          prev shouldEqual StringLiteral("Proof by induction")
          next shouldEqual StringLiteral("Preuve par recurrence")
        }.getOrElse(fail(s"Could not find title in $frMap"))
    }
  }


  /*test("Small translation") {
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
*/

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
  */
}
