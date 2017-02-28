import scala.reflect.runtime.universe.TypeTag
import inox._
import inox.trees._
import inox.trees.dsl._
import Constrainable._

object ImplicitTuples {
  /* Generic combination class. We wish to have everything there, but it is apparently not possible */
  abstract class Combination[Tuple <: Product](constrainables: Constrainable[_]*) extends Constrainable[Tuple] {
    def getType = ADTType(_tupleTypes(constrainables.length - 2), constrainables.map(_.getType))
  }

  /** Combination2 for Tuple2 */
  case class Combination2[A, B](self: Constrainable[A], other: Constrainable[B]) extends Combination[(A, B)](self, other) {
    def recoverFrom(e: Expr): (A, B) = e match {
      case ADT(_, Seq(a, b)) => (self.recoverFrom(a), other.recoverFrom(b))
      case _ => throw new Exception("Could not recover tuple from " + e)
    }
    def produce(a: (A, B)): Expr = ADT(getType, Seq(self.produce(a._1), other.produce(a._2)))
  }

  /** Combination3 for Tuple3 */
  case class Combination3[A, B, C](ca: Constrainable[A], cb: Constrainable[B], cc: Constrainable[C]) extends Combination[(A, B, C)](ca, cb, cc) {
    def recoverFrom(e: Expr): (A, B, C) = e match {
      case ADT(_, Seq(ea, eb, ec)) => (ca.recoverFrom(ea), cb.recoverFrom(eb), cc.recoverFrom(ec))
      case _ => throw new Exception("Could not recover tuple from " + e)
    }
    def produce(a: (A, B, C)): Expr = ADT(getType, Seq(ca.produce(a._1), cb.produce(a._2), cc.produce(a._3)))
  }

  val tuple2 : Identifier = FreshIdentifier("Tuple2")
  val tuple3 : Identifier = FreshIdentifier("Tuple3")
  val tuple4 : Identifier = FreshIdentifier("Tuple4")
  val tuple5 : Identifier = FreshIdentifier("Tuple5")
  val tuple6 : Identifier = FreshIdentifier("Tuple6")
  val tuple7 : Identifier = FreshIdentifier("Tuple7")
  val tuple8 : Identifier = FreshIdentifier("Tuple8")
  val tuple9 : Identifier = FreshIdentifier("Tuple9")
  val tuple10: Identifier = FreshIdentifier("Tuple10")
  val tuple11: Identifier = FreshIdentifier("Tuple11")
  val tuple12: Identifier = FreshIdentifier("Tuple12")
  val tuple13: Identifier = FreshIdentifier("Tuple13")
  val tuple14: Identifier = FreshIdentifier("Tuple14")
  val tuple15: Identifier = FreshIdentifier("Tuple15")
  val tuple16: Identifier = FreshIdentifier("Tuple16")
  val tuple17: Identifier = FreshIdentifier("Tuple17")
  val tuple18: Identifier = FreshIdentifier("Tuple18")
  val tuple19: Identifier = FreshIdentifier("Tuple19")
  val tuple20: Identifier = FreshIdentifier("Tuple20")
  val tuple21: Identifier = FreshIdentifier("Tuple21")
  val tuple22: Identifier = FreshIdentifier("Tuple22")
  val _tupleTypes = List(tuple2, tuple3, tuple4, tuple5, tuple6, tuple7, tuple8, tuple9, tuple10, tuple11, tuple12,
    tuple13, tuple14, tuple15, tuple16, tuple17, tuple18, tuple19, tuple20, tuple21, tuple22)

  val _1 : Identifier = FreshIdentifier("_1")
  val _2 : Identifier = FreshIdentifier("_2")
  val _3 : Identifier = FreshIdentifier("_3")
  val _4 : Identifier = FreshIdentifier("_4")
  val _5 : Identifier = FreshIdentifier("_5")
  val _6 : Identifier = FreshIdentifier("_6")
  val _7 : Identifier = FreshIdentifier("_7")
  val _8 : Identifier = FreshIdentifier("_8")
  val _9 : Identifier = FreshIdentifier("_9")
  val _10: Identifier = FreshIdentifier("_10")
  val _11: Identifier = FreshIdentifier("_11")
  val _12: Identifier = FreshIdentifier("_12")
  val _13: Identifier = FreshIdentifier("_13")
  val _14: Identifier = FreshIdentifier("_14")
  val _15: Identifier = FreshIdentifier("_15")
  val _16: Identifier = FreshIdentifier("_16")
  val _17: Identifier = FreshIdentifier("_17")
  val _18: Identifier = FreshIdentifier("_18")
  val _19: Identifier = FreshIdentifier("_19")
  val _20: Identifier = FreshIdentifier("_20")
  val _21: Identifier = FreshIdentifier("_21")
  val _22: Identifier = FreshIdentifier("_22")
  val _tupleIdentifiers: List[Identifier] = List(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, _20, _21, _22)
  /* The type `T(list)(tp)` is a shorthand for `ADTType(list, Seq(tp))`. */

  type ADTConstructor = inox.trees.dsl.trees.ADTConstructor

  def createTupleConstructor(i: Int): ADTConstructor = {
    mkConstructor(_tupleTypes(i-2))((1 to i).map("B" + _) : _*)(None) { case s => _tupleIdentifiers.zip(s).map{ case (id, tp) => ValDef(id, tp) } }
  }

  val allTupleConstructors = (2::2::(2 to 22).toList) map createTupleConstructor

  val tuple2Constructor: ADTConstructor  = allTupleConstructors(2)
  val tuple3Constructor: ADTConstructor  = allTupleConstructors(3)
  val tuple4Constructor: ADTConstructor  = allTupleConstructors(4)
  val tuple5Constructor: ADTConstructor  = allTupleConstructors(5)
  val tuple6Constructor: ADTConstructor  = allTupleConstructors(6)
  val tuple7Constructor: ADTConstructor  = allTupleConstructors(7)
  val tuple8Constructor: ADTConstructor  = allTupleConstructors(8)
  val tuple9Constructor: ADTConstructor  = allTupleConstructors(9)
  val tuple10Constructor: ADTConstructor = allTupleConstructors(10)
  val tuple11Constructor: ADTConstructor = allTupleConstructors(11)
  val tuple12Constructor: ADTConstructor = allTupleConstructors(12)
  val tuple13Constructor: ADTConstructor = allTupleConstructors(13)
  val tuple14Constructor: ADTConstructor = allTupleConstructors(14)
  val tuple15Constructor: ADTConstructor = allTupleConstructors(15)
  val tuple16Constructor: ADTConstructor = allTupleConstructors(16)
  val tuple17Constructor: ADTConstructor = allTupleConstructors(17)
  val tuple18Constructor: ADTConstructor = allTupleConstructors(18)
  val tuple19Constructor: ADTConstructor = allTupleConstructors(19)
  val tuple20Constructor: ADTConstructor = allTupleConstructors(20)
  val tuple21Constructor: ADTConstructor = allTupleConstructors(21)
  val tuple22Constructor: ADTConstructor = allTupleConstructors(22)
/*
  object RecomposeTuples {
    def unapply[A](t: (A, A)): List[A] = {
      val a = t._1
      val b = t._2
      t match {
        /*case ((a1, a2, a3, a4),
              (b1, b2, b3, b4)) => List(a, b,
              (a1, a2, a3, b4).asInstanceOf[A],
              (a1, a2, b3, b4).asInstanceOf[A],
              (a1, b2, b3, b4).asInstanceOf[A]
              )  : List[A]*/
        case ((a1, a2, a3),
              (b1, b2, b3)) => List(a, b,
              (a1, a2, b3).asInstanceOf[A],
              (a1, b2, b3).asInstanceOf[A])  : List[A]
        case ((a1, a2),
              (b1, b2)) => List(a, b,
              (a1, b2).asInstanceOf[A])  : List[A]
        case _ => List(a, b)
      }
    }
    def unapply3[A](t: (A, A, A)): List[A] = {
      val a = t._1
      val b = t._2
      val c = t._3
      t match {
        case ((a1, a2, a3),
              (b1, b2, b3),
              (c1, c2, c3)) => List(
              (a1, b2, c3).asInstanceOf[A],
              a, b, c)  : List[A]
        case ((a1, a2),
              (b1, b2),
              (c1, c2)) => List(a, b,
              (a1, b2).asInstanceOf[A],
              (a1, c2).asInstanceOf[A],
              (b1, c2).asInstanceOf[A])  : List[A]
        case _ => List(a, b, c)
      }
    }
  }*/
  
  class TupleProducer[A: Constrainable, Tuple <: Product : Constrainable, C: Constrainable] private[ImplicitTuples] (
      val f: A ~~> Tuple, val index: Int)
    extends (A &~> C) {
    def get(in: A): C = f.get(in).productElement(index-1).asInstanceOf[C]
    val name = "Tuple"+index
    override def put(varC: Variable, varA: Variable, in1: Option[A]): Constraint[A] = {
      val selector = _tupleIdentifiers(index-1)
      var varTuple = variable[Tuple]("t", true)
      f.put(varTuple, varA, in1) &&  varTuple.getField(selector) === varC
    }
  }

  implicit class Tuple2Producer[A: Constrainable, B1: Constrainable, B2: Constrainable]
                        (f: A ~~> (B1, B2)) {
    def _1 = new TupleProducer[A, (B1, B2), B1](f, 1)
    def _2 = new TupleProducer[A, (B1, B2), B2](f, 2)
  }
  implicit class Tuple3Producer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable]
                        (f: A ~~> (B1, B2, B3)) {
    def _1 = new TupleProducer[A, (B1, B2, B3), B1](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3), B2](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3), B3](f, 3)
  }
  /*
  implicit class Tuple4Producer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4), B1](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4), B2](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4), B3](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4), B4](f, 4)
  }
  implicit class Tuple5Producer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5), B1](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5), B2](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5), B3](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5), B4](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5), B5](f, 5)
  }
  implicit class Tuple6Producer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6), B1](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6), B2](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6), B3](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6), B4](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6), B5](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6), B6](f, 6)
  }
  implicit class Tuple7Producer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7), B1](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7), B2](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7), B3](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7), B4](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7), B5](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7), B6](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7), B7](f, 7)
  }
  implicit class Tuple8Producer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B1](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B2](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B3](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B4](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B5](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B6](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B7](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B8](f, 8)
  }
  implicit class Tuple9Producer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable, B9: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B1](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B2](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B3](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B4](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B5](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B6](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B7](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B8](f, 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B9](f, 9)
  }
  implicit class Tuple10roducer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable, B9: Constrainable, B10: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B1 ](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B2 ](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B3 ](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B4 ](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B5 ](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B6 ](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B7 ](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B8 ](f, 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B9 ](f, 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B10](f, 10)
  }
  implicit class Tuple11roducer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable, B9: Constrainable, B10: Constrainable, B11: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B1 ](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B2 ](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B3 ](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B4 ](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B5 ](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B6 ](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B7 ](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B8 ](f, 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B9 ](f, 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B10](f, 10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B11](f, 11)
  }
  implicit class Tuple12roducer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable, B9: Constrainable, B10: Constrainable, B11: Constrainable, B12: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B1 ](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B2 ](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B3 ](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B4 ](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B5 ](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B6 ](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B7 ](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B8 ](f, 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B9 ](f, 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B10](f, 10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B11](f, 11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B12](f, 12)
  }
  implicit class Tuple13roducer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable, B9: Constrainable, B10: Constrainable, B11: Constrainable, B12: Constrainable, B13: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B1 ](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B2 ](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B3 ](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B4 ](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B5 ](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B6 ](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B7 ](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B8 ](f, 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B9 ](f, 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B10](f, 10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B11](f, 11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B12](f, 12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B13](f, 13)
  }
  implicit class Tuple14roducer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable, B9: Constrainable, B10: Constrainable, B11: Constrainable, B12: Constrainable, B13: Constrainable, B14: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B1 ](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B2 ](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B3 ](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B4 ](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B5 ](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B6 ](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B7 ](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B8 ](f, 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B9 ](f, 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B10](f, 10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B11](f, 11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B12](f, 12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B13](f, 13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B14](f, 14)
  }
  implicit class Tuple15roducer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable, B9: Constrainable, B10: Constrainable, B11: Constrainable, B12: Constrainable, B13: Constrainable, B14: Constrainable, B15: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B1 ](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B2 ](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B3 ](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B4 ](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B5 ](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B6 ](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B7 ](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B8 ](f, 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B9 ](f, 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B10](f, 10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B11](f, 11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B12](f, 12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B13](f, 13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B14](f, 14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B15](f, 15)
  }
  implicit class Tuple16roducer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable, B9: Constrainable, B10: Constrainable, B11: Constrainable, B12: Constrainable, B13: Constrainable, B14: Constrainable, B15: Constrainable, B16: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B1 ](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B2 ](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B3 ](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B4 ](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B5 ](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B6 ](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B7 ](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B8 ](f, 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B9 ](f, 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B10](f, 10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B11](f, 11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B12](f, 12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B13](f, 13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B14](f, 14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B15](f, 15)
    def _16= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B16](f, 16)
  }
  implicit class Tuple17roducer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable, B9: Constrainable, B10: Constrainable, B11: Constrainable, B12: Constrainable, B13: Constrainable, B14: Constrainable, B15: Constrainable, B16: Constrainable, B17: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B1 ](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B2 ](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B3 ](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B4 ](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B5 ](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B6 ](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B7 ](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B8 ](f, 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B9 ](f, 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B10](f, 10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B11](f, 11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B12](f, 12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B13](f, 13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B14](f, 14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B15](f, 15)
    def _16= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B16](f, 16)
    def _17= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B17](f, 17)
  }
  implicit class Tuple18roducer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable, B9: Constrainable, B10: Constrainable, B11: Constrainable, B12: Constrainable, B13: Constrainable, B14: Constrainable, B15: Constrainable, B16: Constrainable, B17: Constrainable, B18: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B1 ](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B2 ](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B3 ](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B4 ](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B5 ](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B6 ](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B7 ](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B8 ](f, 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B9 ](f, 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B10](f, 10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B11](f, 11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B12](f, 12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B13](f, 13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B14](f, 14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B15](f, 15)
    def _16= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B16](f, 16)
    def _17= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B17](f, 17)
    def _18= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B18](f, 18)
  }
  implicit class Tuple19roducer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable, B9: Constrainable, B10: Constrainable, B11: Constrainable, B12: Constrainable, B13: Constrainable, B14: Constrainable, B15: Constrainable, B16: Constrainable, B17: Constrainable, B18: Constrainable, B19: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B1 ](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B2 ](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B3 ](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B4 ](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B5 ](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B6 ](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B7 ](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B8 ](f, 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B9 ](f, 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B10](f, 10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B11](f, 11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B12](f, 12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B13](f, 13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B14](f, 14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B15](f, 15)
    def _16= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B16](f, 16)
    def _17= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B17](f, 17)
    def _18= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B18](f, 18)
    def _19= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B19](f, 19)
  }
  implicit class Tuple20roducer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable, B9: Constrainable, B10: Constrainable, B11: Constrainable, B12: Constrainable, B13: Constrainable, B14: Constrainable, B15: Constrainable, B16: Constrainable, B17: Constrainable, B18: Constrainable, B19: Constrainable, B20: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B1 ](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B2 ](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B3 ](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B4 ](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B5 ](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B6 ](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B7 ](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B8 ](f, 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B9 ](f, 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B10](f, 10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B11](f, 11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B12](f, 12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B13](f, 13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B14](f, 14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B15](f, 15)
    def _16= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B16](f, 16)
    def _17= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B17](f, 17)
    def _18= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B18](f, 18)
    def _19= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B19](f, 19)
    def _20= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B20](f, 20)
  }
  implicit class Tuple21roducer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable, B9: Constrainable, B10: Constrainable, B11: Constrainable, B12: Constrainable, B13: Constrainable, B14: Constrainable, B15: Constrainable, B16: Constrainable, B17: Constrainable, B18: Constrainable, B19: Constrainable, B20: Constrainable, B21: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B1 ](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B2 ](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B3 ](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B4 ](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B5 ](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B6 ](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B7 ](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B8 ](f, 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B9 ](f, 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B10](f, 10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B11](f, 11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B12](f, 12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B13](f, 13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B14](f, 14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B15](f, 15)
    def _16= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B16](f, 16)
    def _17= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B17](f, 17)
    def _18= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B18](f, 18)
    def _19= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B19](f, 19)
    def _20= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B20](f, 20)
    def _21= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B21](f, 21)
  }
  implicit class Tuple22roducer[A: Constrainable, B1: Constrainable, B2: Constrainable, B3: Constrainable, B4: Constrainable, B5: Constrainable, B6: Constrainable, B7: Constrainable, B8: Constrainable, B9: Constrainable, B10: Constrainable, B11: Constrainable, B12: Constrainable, B13: Constrainable, B14: Constrainable, B15: Constrainable, B16: Constrainable, B17: Constrainable, B18: Constrainable, B19: Constrainable, B20: Constrainable, B21: Constrainable, B22: Constrainable]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B1 ](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B2 ](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B3 ](f, 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B4 ](f, 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B5 ](f, 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B6 ](f, 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B7 ](f, 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B8 ](f, 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B9 ](f, 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B10](f, 10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B11](f, 11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B12](f, 12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B13](f, 13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B14](f, 14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B15](f, 15)
    def _16= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B16](f, 16)
    def _17= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B17](f, 17)
    def _18= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B18](f, 18)
    def _19= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B19](f, 19)
    def _20= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B20](f, 20)
    def _21= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B21](f, 21)
    def _22= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B22](f, 22)
  }*/
}