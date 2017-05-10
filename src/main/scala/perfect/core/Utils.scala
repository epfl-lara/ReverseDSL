package perfect.core

import scala.collection.generic.CanBuildFrom

/**
  * Created by Mikael on 08/05/2017.
  */
class Utils(pu: ProgramUpdater) {
  /** Returns the stream b if a is empty, else only a. */
  def ifEmpty[A](a: Stream[A])(b: =>Stream[A]): Stream[A] = {
    if(a.isEmpty) b else a
  }

  /** Applies the interleaving to a finite sequence of streams. */
  def interleave[A](left: Stream[A])(right: => Stream[A]) : Stream[A] = {
    if (left.isEmpty) right else left.head #:: interleave(right)(left.tail)
  }

  implicit class AugmentedBoolean(e: Boolean) {
    @inline def flatMap[A, T[A]](f: => T[A])(implicit canBuildFrom: CanBuildFrom[T[A], A, T[A]]) = {
      if(e) f else {
        val bf = canBuildFrom.apply()
        bf.result()
      }
    }
  }

  /** Returns a unique name based on the default name and a suffix using alphabet letter to avoid conflicts. */
  def uniqueName(default: String, conflicts: Set[String]): String = {
    var finalName = default
    var suffix = ""
    while(conflicts(finalName + suffix.reverse)) {
      val zs = suffix.takeWhile(c => c == 'z')
      val not_zs = suffix.drop(zs.length)
      val after_zs = if(not_zs.isEmpty) "a" else {
        (not_zs(0) + 1).toChar + not_zs.substring(1)
      }
      suffix = "a"*zs.length + after_zs
    }
    finalName + suffix.reverse
  }

  object StreamUtils {
    /** Interleaves a stream of streams, such that eventually all elements will be enumerated.  */
    def interleaves[A](streams: Stream[Stream[A]]): Stream[A] = {
      def rec(streams: Stream[Stream[A]], diag: Int): Stream[A] = {
        if(streams.isEmpty) Stream() else {
          val (take, leave) = streams.splitAt(diag)
          val (nonEmpty, empty) = take partition (_.nonEmpty)
          nonEmpty.map(_.head) #::: rec(nonEmpty.map(_.tail) ++ leave, diag + 1 - empty.size)
        }
      }
      rec(streams, 1)
    }

    /** Applies the interleaving to a finite sequence of streams. */
    def interleaves[A](streams: Seq[Stream[A]]) : Stream[A] = {
      val nonEmptyStreams = streams.toStream.filter(_.nonEmpty)
      if(nonEmptyStreams.nonEmpty) {
        nonEmptyStreams.map(_.head) #::: interleaves(nonEmptyStreams.map(_.tail))
      } else Stream.empty
    }

    /** Returns the unique number matching the pair (x, y) in cantor bijection*/
    private def cantorPair(x: Int, y: Int): Int = {
      val xpy = x + y
      y + xpy * (xpy + 1) / 2
    }

    /** Returns the pair of numbers corresponding to the given number in cantor bijection.
      * cantorPair.tupled(reverseCantorPair(z)) = z
      * reverseCantorPair(cantorPair.tupled(t)) = t
      * */
    def reverseCantorPair(z: Int): (Int, Int) = {
      import Math._
      val t = floor((sqrt(8f * z + 1f) - 1)/2f).toInt
      val ttp1o2 = t * (t + 1) / 2
      (ttp1o2 + t- z, z - ttp1o2)
    }

    /** Combines two streams into one using cantor's unpairing function.
      *  Ensures that the stream terminates if both streams terminate */
    def cartesianProduct[A, B](sa: Stream[A], sb: Stream[B]): Stream[(A, B)] = {
      def rec(sa: Stream[A], sb: Stream[B])(i: Int): Stream[(A, B)] = {
        val (x, y) = reverseCantorPair(i)
        if(!sa.isDefinedAt(x) && !sb.isDefinedAt(y)) Stream.Empty
        else if(sa.isDefinedAt(x) && sb.isDefinedAt(y)) (sa(x), sb(y)) #:: rec(sa, sb)(i+1)
        else rec(sa, sb)(i+1)
      }
      rec(sa, sb)(0)
    }

    def cartesianProduct[A](streams: Seq[Stream[A]]) : Stream[List[A]] = {
      val dimensions = streams.size
      val vectorizedStreams = streams.map(new VectorizedStream(_))

      if(dimensions == 0)
        return Stream.cons(Nil, Stream.empty)

      if(streams.exists(_.isEmpty))
        return Stream.empty

      val indices = diagCount(dimensions)

      var allReached : Boolean = false
      val bounds : Array[Option[Int]] = for (s <- streams.toArray) yield {
        if (s.hasDefiniteSize) {
          Some(s.size)
        } else {
          None
        }
      }

      indices.takeWhile(_ => !allReached).flatMap { indexList =>
        var d = 0
        var continue = true
        var is = indexList
        var ss = vectorizedStreams.toList

        if ((indexList zip bounds).forall {
          case (i, Some(b)) => i >= b
          case _ => false
        }) {
          allReached = true
        }

        var tuple : List[A] = Nil

        while(continue && d < dimensions) {
          val i = is.head
          if(bounds(d).exists(i > _)) {
            continue = false
          } else try {
            // TODO can we speed up by caching the random access into
            // the stream in an indexedSeq? After all, `i` increases
            // slowly.
            tuple = ss.head(i) :: tuple
            is = is.tail
            ss = ss.tail
            d += 1
          } catch {
            case e : IndexOutOfBoundsException =>
              bounds(d) = Some(i - 1)
              continue = false
          }
        }
        if(continue) Some(tuple.reverse) else None
      }
    }

    private def diagCount(dim : Int) : Stream[List[Int]] = diag0(dim, 0)
    private def diag0(dim : Int, nextSum : Int) : Stream[List[Int]] = summingTo(nextSum, dim).append(diag0(dim, nextSum + 1))

    private def summingTo(sum : Int, n : Int) : Stream[List[Int]] = {
      // assert(sum >= 0)
      if(sum < 0) {
        Stream.empty
      } else if(n == 1) {
        Stream.cons(sum :: Nil, Stream.empty)
      } else {
        (0 to sum).toStream.flatMap(fst => summingTo(sum - fst, n - 1).map(fst :: _))
      }
    }

    private class VectorizedStream[A](initial : Stream[A]) {
      private def mkException(i : Int) = new IndexOutOfBoundsException("Can't access VectorizedStream at : " + i)
      private def streamHeadIndex : Int = indexed.size
      private var stream  : Stream[A] = initial
      private var indexed : Vector[A] = Vector.empty

      def apply(index : Int) : A = {
        if(index < streamHeadIndex) {
          indexed(index)
        } else {
          val diff = index - streamHeadIndex // diff >= 0
          var i = 0
          while(i < diff) {
            if(stream.isEmpty) throw mkException(index)
            indexed = indexed :+ stream.head
            stream  = stream.tail
            i += 1
          }
          // The trick is *not* to read past the desired element. Leave it in the
          // stream, or it will force the *following* one...
          stream.headOption.getOrElse { throw mkException(index) }
        }
      }
    }
  }
}
