package perfect.core.predef

import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer

/**
  * Created by Mikael on 23/03/2017.
  */
trait FilterLike[A] {
  def filter(l: List[A], f: A => Boolean): List[A] = l filter f

  /** Returns true if l filtered is equal to out. */
  @tailrec private def equalFilter(l: List[A], b: List[Boolean], out: List[A]): Boolean = {
    l match {
      case head :: tail => if(b.head) (
        if(!out.isEmpty && out.head == head) equalFilter(tail, b.tail, out.tail)
        else false) else equalFilter(tail, b.tail, out)
      case Nil => out.isEmpty
    }
  }

  @tailrec private def keepIfFalse(l: List[A], b: List[Boolean], result: List[A] = Nil): List[A] = l match {
    case head::tail =>
      if(!b.head) keepIfFalse(tail, b.tail, head::result)
      else keepIfFalse(tail, b.tail, result)
    case Nil => result.reverse
  }

  @tailrec private def filterRevAux(l: List[A], lPass: List[Boolean], out: List[A], prepend: ListBuffer[A]): Stream[List[A]] = {
    if (equalFilter(l, lPass, out)) Stream(prepend.toList ++ l) else
      l match {
        case Nil => Stream(prepend.toList ++ out)
        case hd::tl =>
          if(!lPass.head) {
            filterRevAux(tl, lPass.tail, out, prepend += hd)
          } else { // hd has to be kept
            out match {
              case Nil => // Everything was deleted ! We keep only the elements that could not have appeared in out
                Stream(keepIfFalse(tl, lPass.tail))
              case outhd::outtl =>
                if(outhd == hd) { // The element is the same.
                  filterRevAux(tl, lPass.tail, outtl, prepend += outhd)
                } else { // Find if elements have been deleted.
                  // hd != outhd, either we can find it later or it has been deleted.
                  val expectedFiltered_l = l.zip(lPass).filter(_._2).map(_._1)
                  val k = out.indexOfSlice(expectedFiltered_l)
                  if(k > 0) { // There has been some additions in out, we add them directly.
                    filterRevAux(l, lPass, out.drop(k), prepend ++= out.take(k))
                  } else {
                    val k2 = expectedFiltered_l.indexOfSlice(out)
                    if(k2 > 0) { // There has been some deletions in out.
                      // Maybe some elements have been deleted.
                      filterRevAux(tl, lPass.tail, out, prepend)
                    } else { // Exact number of same elements, we replace them directly.
                      filterRevAux(tl, lPass.tail, out.tail, prepend += outhd)
                    }
                  }
                }
            }
          }
      }
  }

  def filterRev(l: List[A], f: A => Boolean, out: List[A]): Stream[List[A]] = {
    filterRevAux(l, l.map(f), out, ListBuffer())
  }
}
