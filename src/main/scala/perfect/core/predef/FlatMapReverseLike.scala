package perfect.core.predef

/**
  * Created by Mikael on 29/03/2017.
  */

trait FlatMapReverseLike[A, B, F] {
  def f: A => List[B]
  def fRev: (Option[A], List[B]) => Stream[Either[A, F]]

  def flatMap(l: List[A]): List[B] = l.flatMap(f)

  // Split lOut into three components:
  // The parts which are rendered correctly in out (first and last value)
  // The parts which differ from out. Empty if elements have been removed.
  private def recombine(lOut: List[List[B]], out: List[B]): (List[List[B]], List[B], List[List[B]]) = {
    lOut match {
      case Nil => (Nil, out, Nil)
      case lOutHead::tail =>
        if(out.startsWith(lOutHead)) {
          val (before, middle, after) = recombine(lOut.tail, out.drop(lOutHead.length))
          (lOutHead :: before, middle, after)
        } else {
          val optI = (0 to lOut.length).find { i =>
            out.endsWith(lOut.drop(i).flatten)
          }
          assert(optI.isInstanceOf[Some[Int]], "[Internal error] should not happen")
          val i = optI.asInstanceOf[Some[Int]].get
          val after = lOut.drop(i)
          (Nil, out.take(out.length - after.flatten.length), after)
        }
    }
  } /: perfect.Log.prefix(s"recombine($lOut, $out)=")

  // Shortcut to quickly isolate parts which have changed.
  private def flatMapRevAuxInit(l: List[A], lOut: List[List[B]], out: List[B]): Stream[List[Either[A, F]]] = {
    val (before, middle, after) = recombine(lOut, out)
    val beforeA: List[Either[A, F]] = l.take(before.length).map(x => Left[A, F](x))
    val afterA: List[Either[A, F]] = l.drop(l.length - after.length).map(x => Left[A, F](x))

    // Elements which have changed.
    val afterChanged: List[B] = middle

    if(afterChanged.isEmpty) { // Elements have simplfy been deleted.
      Stream(beforeA ++ afterA)
    } else {
      val beforeChanged: List[A] = l.slice(before.length, l.length - after.length)
      val beforeChangedOut: List[List[B]] = lOut.slice(before.length, l.length - after.length)

      perfect.Log("List before not changed:"+beforeA)
      perfect.Log("List after not changed:"+afterA)
      for(s <- flatMapRevAux(beforeChanged, beforeChangedOut, afterChanged)) yield {
        beforeA ++ s ++ afterA
      }
    }
  }

  private def flatMapRevAux(l: List[A], lOut: List[List[B]], out: List[B]): Stream[List[Either[A, F]]] = {
    perfect.Log(s"Repairing $l = $lOut => $out")
    l match {
      case Nil =>
        out match {
          case Nil => Stream(Nil)
          case _ => // All possibilities !
            for{i <- (out.length to 1 by -1).toStream
                out_take_i = out.take(i)
                a <- fRev(None, out_take_i)
                sol <- flatMapRevAux(l, lOut, out.drop(i))} yield {
              a::sol
            }
        }
      case ha::tail =>
        val expectedout = lOut.head
        if(expectedout.isEmpty) {
          flatMapRevAux(tail, lOut.tail, out).map(Left(ha)::_)
        } else if(out == expectedout) {
          flatMapRevAux(tail, lOut.tail, Nil).map(Left(ha)::_)
        } else if(out.take(expectedout.length) == expectedout) { // There has been an addition at the end
          val t = flatMapRevAux(tail, lOut.tail, out.drop(expectedout.length)).map(Left(ha) :: _)
          if (t.isEmpty) { // Fallback: We completely remove the hint
            flatMapRevAux(Nil, Nil, out)
          } else t
        } else if(out.drop(expectedout.length) == lOut.tail.flatten) { // The elements for this particular item have changed.
          for{ a <- fRev(Some(l.head), out.take(expectedout.length)) } yield {
            a:: l.tail.map(x => Left[A, F](x))
          }
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
    flatMapRevAuxInit(l, l.map(f), out)
  }
}

