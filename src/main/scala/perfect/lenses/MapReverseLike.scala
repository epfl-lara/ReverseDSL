package perfect.lenses

/**
  * Created by Mikael on 23/03/2017.
  */

// The F parameter allows to modify the mapping function itself.
trait MapReverseLike[A, B, F] {
  def map(l: List[A]): List[B] = l map f

  def f: A => B
  def fRev: (Option[A], B) => Stream[Either[A, F]]

  def combinatorialMap(l: List[B]): Stream[List[Either[A, F]]] =
    l match {
      case Nil => Stream(Nil)
      case a::b =>
        fRev(None, a).flatMap(fb => combinatorialMap(b).map(fb::_))
    }

  private def mapRevAux(l: List[A], lOut: List[B], out: List[B]): Stream[List[Either[A, F]]] = {
    l match {
      case Nil =>
        out match {
          case Nil => Stream(Nil)
          case outhd::outtail =>
            val revOutHd = fRev(None, outhd)
            for{ sol <- mapRevAux(l, lOut, outtail)
                 other_a <- revOutHd } yield {
              other_a :: sol
            }
        }
      case hd::tl =>
        out match {
          case Nil => Stream(Nil)
          case outhd::outtail =>
            if(lOut.head == outhd) { // The out element is the right one, we don't touch it.
              mapRevAux(l.tail, lOut.tail, out.tail).map(Left(hd)::_)
            } else {
              val k = lOut.indexOfSlice(out)
              if (k > 0) { // There has been a deletion, but we are able to find the remaining elements.
                mapRevAux(l.drop(k), lOut.drop(k), out)
              } else {
                val k2 = out.indexOfSlice(lOut)
                if (k2 > 0) { // Some elements were added at some point.
                val tailSolutions = mapRevAux(l, lOut, out.drop(k2))
                  // Now for each of out.take(k2), we take all possible inverses.
                  combinatorialMap(out.take(k2)).flatMap(l => tailSolutions.map(l ++ _))
                } else { // No deletion, no insertion, hence modifications.
                  fRev(Some(hd), outhd).flatMap(s => mapRevAux(tl, lOut.tail, outtail).map(s :: _))
                }
              }
            }
        }
    }
  }

  def mapRev(l: List[A], out: List[B]): Stream[List[Either[A, F]]] = {
    mapRevAux(l, l.map(f), out)
  }
}
