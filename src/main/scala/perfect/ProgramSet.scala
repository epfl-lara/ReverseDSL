/**
  * Created by Mikael on 15/03/2017.
  */
/*abstract class ProgramSet[A] { self =>
  def toStream: Stream[A]
  def toStreamWithExplanation: Stream[(A, String)]

  def filter(pred: A => Boolean): ProgramSet[A] = {
    new ProgramSet[A] {
      def toStream = self.toStream.filter(pred)

      def toStreamWithExplanation = self.toStreamWithExplanation.filter(x => pred(x._1)).map(x => (x._1, x._2 + "\n + filtered"))
    }
  }
  def map[B](f: A => B): ProgramSet[B] = {
    new ProgramSet[B] {
      def toStream = self.toStream.map(f)

      def toStreamWithExplanation = self.toStreamWithExplanation.map(x => (f(x._1), x._2 + "\n + mapped"))
    }
  }
  def flatMap[B](f: A => Seq[B]): ProgramSet[B] = {
    new ProgramSet[B] {
      def toStream = self.toStream.flatMap(f)

      def toStreamWithExplanation = self.toStreamWithExplanation.map(x => (f(x._1), x._2 + "\n + mapped"))
    }
  }
}

abstract class JoinProgramSet2[A](left: ProgramSet[A], right: ProgramSet[A]) extends ProgramSet[A] {
  def combine(a: A, b: A): A
  def toStream = inox.utils.StreamUtils.cartesianProduct[A, A](left.toStream, right.toStream).map(x => combine(x._1, x._2))

  def toStreamWithExplanation = {
    inox.utils.StreamUtils.cartesianProduct(left.toStreamWithExplanation, right.toStreamWithExplanation)
      .map((x: ((A, String), (A, String))) => (combine(x._1._1, x._2._1), x._1._2 + "\n" + x._2._2))
  }
}

abstract class JoinProgramSet[A](joins: Seq[ProgramSet[A]]) extends ProgramSet[A] {
  val combine: Seq[A] => A
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
  def toStreamWithExplanation = toStream.map(x => (x, ""))
}*/
