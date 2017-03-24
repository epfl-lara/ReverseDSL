package perfect

import scala.collection.{GenTraversableOnce, TraversableLike, mutable}
import scala.collection.generic.CanBuildFrom

/**
  * Created by Mikael on 15/03/2017.
  */

/*
object ProgramSet {
  implicit def bf[A, B] = new CanBuildFrom[ProgramSet[A], B, ProgramSet[B]] {
    override def apply(from: ProgramSet[A]) = new mutable.LazyBuilder[B, ProgramSet[B]] {
      override def result(): ProgramSet[B] = ???//JoinProgramSet(from)
    }

    override def apply() = new mutable.LazyBuilder[B, ProgramSet[B]] {
      override def result(): ProgramSet[B] = ???
    }
  }
}

abstract class ProgramSet[A] { self =>
  import ProgramSet._
  def toStream: Stream[A]
  def toStreamWithExplanation: Stream[(A, String)]
  var explanation = ""

  /** Wrapper to give an explanation to the stream */
  def because(eureka: String): this.type = {
    explanation = explanation + "\n"
    this
  }

  def explains_:(eureka: String): this.type = this.because(eureka)

  def flatMap[B, That](f: (A) => ProgramSet[B])(implicit bf: CanBuildFrom[ProgramSet[A], B, That]): That = {
    val lazyBuilder: mutable.Builder[B, That] = bf.apply(this)
    ???
  }
  def map[B, That](f: (A) => B)(implicit bf: CanBuildFrom[ProgramSet[A], B, That]): That = ???
  def filter(p: A => Boolean): ProgramSet[A] = {
    toStream.filter(p)
  }
  def withFilter(p: A => Boolean): ProgramSet[A] = toStream.filter(p);
}

case class JoinProgramSet2[A](left: ProgramSet[A], right: ProgramSet[A])(combine: (A, A) => A) extends ProgramSet[A] {
  def toStream = inox.utils.StreamUtils.cartesianProduct[A, A](left.toStream, right.toStream).map(x => combine(x._1, x._2))

  def toStreamWithExplanation = {
    inox.utils.StreamUtils.cartesianProduct(left.toStreamWithExplanation, right.toStreamWithExplanation)
      .map((x: ((A, String), (A, String))) => (combine(x._1._1, x._2._1), x._1._2 + "\n" + x._2._2))
  }
}

case class JoinProgramSet[A](joins: Seq[ProgramSet[A]])(combine: Seq[A] => A) extends ProgramSet[A] {
  def toStream = inox.utils.StreamUtils.cartesianProduct[A](joins.map(_.toStream)).map(x => combine(x))

  def toStreamWithExplanation = {
    inox.utils.StreamUtils.cartesianProduct(joins.map(_.toStreamWithExplanation))
      .map((x: Seq[(A, String)]) => (combine(x.map(_._1)), x.map(_._2).mkString("\n")))
  }
}

case class UnionProgramSet[A](unions: Seq[ProgramSet[A]]) {
  def toStream = inox.utils.StreamUtils.interleave(unions.map(_.toStream))
}

case class DirectProgramSet[A](a: A) extends ProgramSet[A] {
  def toStream = Stream(a)
  def toStreamWithExplanation = toStream.map(x => (x, explanation))
}

/** Filter the results of a program set according to a boolean expression */
case class FilterProgramSet[A](i: ProgramSet[A], f: A => Boolean)
    extends ProgramSet[A] {
  def toStream = i.toStream.filter(f)

  def _explanations(i: Stream[(A, String)], previousFailed: String): Stream[(A, String)] = {
    if(i.isEmpty) {
      Log("End of stream")
      return Stream.empty
    }
    val (x, ex) = i.head
    if(f(x)) {
      (x, previousFailed + ex + "\n" + this.explanation + " (passed)") #:: {
        _explanations(i.tail, "")
      }
    } else {
      _explanations(i.tail, previousFailed + ex + "\n" + this.explanation + " (failed)")
    }
  }
  def toStreamWithExplanation = _explanations(i.toStreamWithExplanation, "")
}*/