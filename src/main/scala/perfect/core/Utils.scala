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
  def interleave[T](left: Stream[T])(right: => Stream[T]) : Stream[T] = {
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
}
