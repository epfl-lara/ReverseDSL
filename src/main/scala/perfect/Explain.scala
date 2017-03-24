package perfect

/**
  * Created by Mikael on 24/03/2017.
  */
import scala.collection.generic.CanBuildFrom

/** Wrapper around any collection, to use in for-comprehensions to debug execution.
  */
case class Explain[A, T[A] <: Traversable[A]](i: T[A], comment: String = "") {
  if(comment != "") Log(comment)

  def toStream = i.toStream
  def toList = i.toList

  def map[B](f: A => (B, String))(implicit cbf   : CanBuildFrom[T[A], B, T[B]]): Explain[B, T] = {
    val builder = cbf()
    val res = for{j <- i
                  fj = f(j)} yield {
      Log(fj._2)
      fj._1
    }
    builder ++= res
    Explain(builder.result)
  }
  def flatMap[B, TT[B] <: Traversable[B]](f: A => Explain[B, TT])(implicit cbf   : CanBuildFrom[T[A], B, TT[B]]): Explain[B, TT] = {
    val builder = cbf()
    val res = for{a <- i
                  eb = f(a)
                  b <- eb.i
    } yield {
      b
    }
    builder ++= res
    Explain(builder.result)
  }
  def filter(f: A => (Boolean, String))(implicit cbf   : CanBuildFrom[T[A], A, T[A]]): Explain[A, T] = {
    val builder = cbf()
    val res = for{a <- i
                  (cond, s) = f(a)
                  _ = Log(s + ": " + cond)
                  if cond} yield {
      a
    }
    builder ++= res
    Explain(builder.result)
  }

  def withFilter(f: A => (Boolean, String))(implicit cbf   : CanBuildFrom[T[A], A, T[A]]): Explain[A, T] = {
    filter(f)
  }
}

/**
for{i <- Explain(List(1, 2, 3)) if (i % 2 == 1) -> s"$i is odd" } yield i -> s"Return $i"

for{
    i <- Explain(Stream(1, 2, 3, 4, 5, 6), "Initial Creation") if (i % 2 == 1) -> s"$i is odd"
    j <- Explain((1 to i).toStream, s"Create stream from 1 to $i")// -> s"Enumerating numbers 1 to $i")
} yield j -> s"Return $j"
  */