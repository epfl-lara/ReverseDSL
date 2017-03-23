package legacy

import inox.Identifier
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._

import perfect.InoxConvertible
import InoxConvertible._
import perfect.ImplicitTuples._
import Implicits._
import perfect.Utils._

/**
  * Created by Mikael on 23/03/2017.
  */
object ImplicitTuples {
  class TupleProducer[A: InoxConvertible, Tuple <: Product : InoxConvertible, C: InoxConvertible] private[ImplicitTuples](
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

  implicit class Tuple2Producer[A: InoxConvertible, B1: InoxConvertible, B2: InoxConvertible]
  (f: A ~~> (B1, B2)) {
    def _1 = new TupleProducer[A, (B1, B2), B1](f, 1)
    def _2 = new TupleProducer[A, (B1, B2), B2](f, 2)
  }
  implicit class Tuple3Producer[A: InoxConvertible, B1: InoxConvertible, B2: InoxConvertible, B3: InoxConvertible]
  (f: A ~~> (B1, B2, B3)) {
    def _1 = new TupleProducer[A, (B1, B2, B3), B1](f, 1)
    def _2 = new TupleProducer[A, (B1, B2, B3), B2](f, 2)
    def _3 = new TupleProducer[A, (B1, B2, B3), B3](f, 3)
  }
}
