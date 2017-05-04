package perfect
import inox._
import inox.trees.{not => dnot, _}
import inox.trees.dsl._
import org.scalatest._
import matchers._
import Matchers.{=== => _, _}

import scala.annotation.tailrec

/**
  * Created by Mikael on 24/04/2017.
  */
class LambdaCalculusTest extends FunSuite with TestHelpers {
  import InoxConvertible._
  import XmlTrees._
  import StringConcatExtended._
  import ProgramFormula.{AssociativeInsert, StringInsert, ListInsert, TreeWrap, TreeUnwrap, TreeModification, CloneText, PasteVariable}

  val churchIntegerTupledType = inoxTypeOf[((Int => Int), Int) => Int]
  val churchIntegerType = inoxTypeOf[(Int => Int) => Int => Int]
  object ChurchInt {
    object tupled {
      def apply(i: Int) =
        \("f"::inoxTypeOf[Int => Int], "x"::inoxTypeOf[Int])( (f, x) => ((x: Expr) /: (1 to i)) { case (e, _) => Application(f, Seq(e)) } )
      def unapply(e: Expr): Option[Int] = e match {
        case Lambda(Seq(f, x), body) =>
          extract(body, x.toVariable, f.toVariable, 0)
        case _ => None
      }
    }
    def apply(i: Int) =
      \("f"::inoxTypeOf[Int => Int])(f => \("x"::inoxTypeOf[Int])( x => ((x: Expr) /: (1 to i)) { case (e, _) => Application(f, Seq(e)) } ))
    @tailrec private def extract(body: Expr, X: Variable, F: Variable, total: Int): Option[Int] = body match {
      case X => Some(total)
      case Application(F, Seq(body2)) => extract(body2, X, F, total + 1)
      case _ => None
    }
    def unapply(e: Expr): Option[Int] = e match {
      case Lambda(Seq(f), Lambda(Seq(x), body)) =>
        extract(body, x.toVariable, f.toVariable, 0)
      case _ => None
    }
  }

  abstract class ConcreteChurchIntBuilder(Value: Int) {
    def apply() = ChurchInt(Value)
    def unapplySeq(e: Expr): Option[Seq[Unit]] = e match {
      case ChurchInt(Value) => Some(Seq())
      case _ => None
    }
    object tupled {
      def apply() = ChurchInt.tupled(Value)
      def unapplySeq(e: Expr): Option[Seq[Unit]] = e match {
        case ChurchInt.tupled(Value) => Some(Seq())
        case _ => None
      }
    }
  }

  object Zero extends ConcreteChurchIntBuilder(0)
  object One extends ConcreteChurchIntBuilder(1)
  object Two extends ConcreteChurchIntBuilder(2)
  object Plus {
    object tupled {
      def apply(): Expr = \("P"::churchIntegerTupledType, "Q"::churchIntegerTupledType)( (P, Q) =>
        \("f"::inoxTypeOf[Int => Int], "x"::inoxTypeOf[Int])( (f, x) => Application(P, Seq(f, Application(Q, Seq(f, x)))))
      )
      def unapplySeq(e: Expr): Option[Seq[Unit]] = e match {
        case Lambda(Seq(p, q), Lambda(Seq(f, x),
        Application(p2, Seq(f2, Application(q2, Seq(f3, x2))))))
          if p.toVariable == p2 && q.toVariable == q2 && f.toVariable == f2 && f2 == f3 && x.toVariable == x2 => Some(Seq())
        case Lambda(Seq(p, q), e) => Log(s"Correct, but $e is not correct")
          None
        case _ => None
      }
    }
    def apply(): Expr = \("P"::churchIntegerType)( P =>
      \("Q"::churchIntegerType)( Q =>
        \("f"::inoxTypeOf[Int => Int])(f => \("x"::inoxTypeOf[Int])( x => Application(Application(P, Seq(f)), Seq(Application(Application(Q, Seq(f)), Seq(x)))) ))
      )
    )
    def unapplySeq(e: Expr): Option[Seq[Unit]] = e match {
      case Lambda(Seq(p), Lambda(Seq(q), Lambda(Seq(f), Lambda(Seq(x),
      Application(Application(p2, Seq(f2)), Seq(Application(Application(q2, Seq(f3)), Seq(x2))))
      )))) if p.toVariable == p2 && q.toVariable == q2 && f.toVariable == f2 && f2 == f3 && x.toVariable == x2 => Some(Seq())
      case _ => None
    }
  }

  object Add {
    def apply(p: Expr, q: Expr): Expr = Application(Application(Plus(), Seq(p)), Seq(q))
    def unapply(e: Expr): Option[(Expr, Expr)] = e match {
      case Application(Application(Plus(), Seq(p)), Seq(q)) => Some((p, q))
      case _ => None
    }
    object tupled {
      def apply(p: Expr, q: Expr): Expr = Application(Plus.tupled(), Seq(p,q))
      def unapply(e: Expr): Option[(Expr, Expr)] = e match {
        case Application(Plus.tupled(), Seq(p, q)) => Some((p, q))
        case Application(e, Seq(p, q)) => Log(s"correct application but $e is not a Plus.tupled")
          None
        case _ => None
      }
    }
  }

  object ChurchToInt {
    def apply(churchInt: Expr) = Application(Application(churchInt, Seq(\("n"::inoxTypeOf[Int])(n => n + 1))), Seq(IntLiteral(0)))
    object tupled {
      def apply(churchIntTupled: Expr) = Application(churchIntTupled, Seq(\("n"::inoxTypeOf[Int])(n => n + 1), IntLiteral(0)))
    }
  }

  test("Lambda calculus computations") {
    ChurchToInt(Add(Zero(), One())) shouldProduce IntLiteral(1)
    ChurchToInt.tupled(Add.tupled(Zero.tupled(), One.tupled())) shouldProduce IntLiteral(1)
    ChurchToInt(Add(One(), One())) shouldProduce IntLiteral(2)
    ChurchToInt.tupled(Add.tupled(One.tupled(), One.tupled())) shouldProduce IntLiteral(2)
  }
  test("Lambda calculus repair 0 -> 2") {
    ChurchToInt(Zero()) repairFrom ChurchToInt(Two()) shouldProduce IntLiteral(2)
    Zero.tupled() repairFrom Two.tupled() match {
      case Two.tupled() => // Ok
    }
  }
  /*test("Lambda calculus repair 0+1 = 2") {
    val pfun = Add(Zero(), One())
    repairProgramList(pfun, Two(), 2).take(2).toList.map[Int, List[Int]] {
      case Add(Zero(), Two()) => 1
      case Add(One(), One()) => 2
    }.toList.sum shouldEqual 3
  }*/

  test("Lambda calculus tupled repair 0+1 = 2") {
    val pfun = Add.tupled(Zero.tupled(), One.tupled())
    ReverseProgram.experimentalUnifyLambda = true
    repairProgramList(pfun, Two.tupled(), 2).take(2).toList.map[Int, List[Int]] {
      case Add.tupled(Zero.tupled(), Two.tupled()) => 1
      case Add.tupled(One.tupled(), One.tupled()) => 2
      case e => fail("Unexpected result: " + e)
    }.sum shouldEqual 3
    ReverseProgram.experimentalUnifyLambda = false
  }

  test("Lambda calculus tupled repair 1+0 = 2") {
    val pfun = Add.tupled(One.tupled(), Zero.tupled())
    ReverseProgram.experimentalUnifyLambda = true
    repairProgramList(pfun, Two.tupled(), 2).take(2).toList.map[Int, List[Int]] {
      case Add.tupled(Two.tupled(), Zero.tupled()) => 1
      case Add.tupled(One.tupled(), One.tupled()) => 2
      case e => fail("Unexpected result: " + e)
    }.toList.sum shouldEqual 3
    ReverseProgram.experimentalUnifyLambda = false
  }

  test("Lambda calculus tupled repair 1+1 = 1") {
    val pfun = Add.tupled(One.tupled(), One.tupled())
    ReverseProgram.experimentalUnifyLambda = true
    repairProgramList(pfun, One.tupled(), 2).take(2).toList.map[Int, List[Int]] {
      case Add.tupled(One.tupled(), Zero.tupled()) => 1
      case Add.tupled(Zero.tupled(), One.tupled()) => 2
      case e => fail("Unexpected result: " + e)
    }.toList.sum shouldEqual 3
    ReverseProgram.experimentalUnifyLambda = false
  }
}
