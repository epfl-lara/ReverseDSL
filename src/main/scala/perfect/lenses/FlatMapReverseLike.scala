package perfect.lenses

/**
  * Created by Mikael on 29/03/2017.
  */

trait FlatMapReverseLike[A, B, F] {
  def f: A => List[B]
  def fRev: (Option[A], List[B]) => Stream[Either[A, F]]

  def flatMap(l: List[A]): List[B] = l.flatMap(f)

  private def flatMapRevAux(l: List[A], lOut: List[List[B]], out: List[B]): Stream[List[Either[A, F]]] = {
    l match {
      case Nil =>
        out match {
          case Nil => Stream(Nil)
          case _ => // All possibilities !
            for{i <- (1 to out.length).toStream
                out_take_i = out.take(i)
                a <- fRev(None, out_take_i)
                sol <- flatMapRevAux(l, lOut, out.drop(i))} yield {
              a::sol
            }
        }
      case ha::tail =>
        val expectedout = lOut.head
        if(expectedout.length == 0) {
          flatMapRevAux(tail, lOut.tail, out).map(Left(ha)::_)
        } else if(out == expectedout) {
          flatMapRevAux(tail, lOut.tail, Nil).map(Left(ha)::_)
        } else if(out.take(expectedout.length) == expectedout) { // There has been an addition at the end
          val t = flatMapRevAux(tail, lOut.tail, out.drop(expectedout.length)).map(Left(ha)::_)
          if(t.isEmpty) { // Fallback: We completely remove the hint
            flatMapRevAux(Nil, Nil, out)
          } else t
        } else {
          val k = out.indexOfSlice(lOut.flatten)
          if(k > 0) {
            val frevouttakek = fRev(None, out.take(k))
            val t = for{ sol <- flatMapRevAux(tail, lOut.tail, out.drop(k + expectedout.length))
                         a <- frevouttakek
            } yield {
              a::Left(ha)::sol
            }
            if(t.isEmpty) {
              flatMapRevAux(Nil, Nil, out)
            } else t
          } else {
            flatMapRevAux(tail, lOut.tail, out)
          }
        }
    }
  }

  def flatMapRev(l: List[A], out: List[B]): Stream[List[Either[A, F]]] = {
    flatMapRevAux(l, l.map(f), out)
  }
}

