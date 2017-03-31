package perfect

import scala.collection.mutable.ArrayBuffer

object Distances extends Distances

object DistanceExpr extends Distances {
  import inox.trees._
  override def size(a: Any): Int = a match {
    case e: Expr => e.toString.length
    case e => super.size(a)
  }
  override def distance(a: Any, b: Any): Int = (a, b) match {
    case (StringConcat(aa, ab), b) if aa == b => size(b) + 3 // Wrapping should not cost too much.
    case (StringConcat(aa, ab), b) if ab == b => size(b) + 3
    case _ => super.distance(a, b)
  }
}

trait Distances {
  def size(a: Any): Int = a match {
    case a: List[_] => (6 /: a) { case (s, x) => (if(s == 6) s else s + 2) + size(x)}
    case a@None => 4
    case a@Nil => 3
    case a: TraversableOnce[_] =>
      val constSize = a.getClass.getSimpleName.length
      ((constSize+2) /: a) { case (s, x) => (if(s == constSize + 2) s else s+2) + size(x) }
    case s: String => s.length + 2
    case 0 => 1
    case i: Int if i > 0 => Math.floor(Math.log(i)/Math.log(10) + 1).toInt
    case i: Int if i < 0 => Math.floor(Math.log(-i)/Math.log(10) + 2).toInt
    case b: Boolean => if(b) 4 else 5
    case p: Product =>
      val constSize = p.getClass.getSimpleName.length
    ((constSize + 2) /: (0 until p.productArity)) {
      case (s, n) => (if(s == constSize + 2) s else s + 2) +size(p.productElement(n))
    }
    case c: Char => 3
    case _ => a.toString.length
  }
  
  def innerSize(a: Any): Int = a match {
    case a: Char => 1
    case s: collection.immutable.StringOps => s.length
    case e => size(a)
  }

  def distance(a: Any, b: Any): Int = {
    if (a == b) 0 else {
//      println(s"computing distance between $a and $b")
//      println(s"Comparing $a of type ${a.getClass}, $b of type ${b.getClass}")
      (a, b) match {
        case (a: Char, b: Char) => 2 // Remove a and write b
        case (a: String, b: String) => Levenshtein.distance(a, b, distance, size)
        case (a: TraversableOnce[_], b: TraversableOnce[_]) => Levenshtein.distance(a, b, distance, size)
        case (a: Product, b: Product) =>
          if (a.getClass == b.getClass || a.productPrefix == b.productPrefix) {
            (0 /: (0 until a.productArity)) {
              case (s, i) => s + distance(a.productElement(i), b.productElement(i))
            }
          } else {
            //println(s"Comparing two non-related products: $a of type ${a.getClass}, $b of type ${b.getClass}")
            size(a) + size(b) // remove a and write b
          }
        case (true, false) => 4
        case (false, true) => 4
        case (a: Int, b: Int) =>
          distance(a.toString, b.toString)
        case (a, b) =>
          //println(s"Comparing two non-related objects: $a, $b")
          size(a) + size(b)
      }
    }
  }

  @inline def differentSpaceChar(a: Char, b: Char): Boolean = {
    val isASpaceChar = a.isSpaceChar
    val isBSpaceChar = b.isSpaceChar
    isASpaceChar && !isBSpaceChar || !isASpaceChar && isBSpaceChar
  }

  @inline def spaceJump(a: String, b: String): Boolean = {
    a.nonEmpty && b.nonEmpty && differentSpaceChar(a(a.length - 1), b(0))
  }

  def distanceWithoutSubstitution(a: Any, b: Any): Int = {
    if (a == b) 0 else {
      (a, b) match {
        case (a: Char, b: Char) =>
          if(differentSpaceChar(a, b)) 3 else 2
        case (a: String, b: String) => Levenshtein.distance(a, b, distanceWithoutSubstitution, size)
        case (a: TraversableOnce[_], b: TraversableOnce[_]) => Levenshtein.distance(a, b, distanceWithoutSubstitution, size)
        case (a: Product, b: Product) =>
          if (a.getClass == b.getClass) {
            (0 /: (0 until a.productArity)) {
              case (s, i) => s + distanceWithoutSubstitution(a.productElement(i), b.productElement(i))
            }
          } else {
            size(a) + size(b) // remove a and write b
          }
        case (true, false) => 4
        case (false, true) => 4
        case (a: Int, b: Int) =>
          distanceWithoutSubstitution(a.toString, b.toString)
        case (a, b) => size(a) + size(b)
      }
    }
  }
 
  object Levenshtein {
    import scala.math._
    def minimum(i1: Int, i2: Int, i3: Int)=min(min(i1, i2), i3)
    /*def distance(ss: TraversableOnce[Any], tt: TraversableOnce[Any]): Int = {
        // degenerate cases
        if (ss == tt) return 0
        if (ss.isEmpty) return size(tt)
        if (tt.isEmpty) return size(ss)
        val s = ss.toIndexedSeq
        val t = tt.toIndexedSeq

        // create two work vectors of integer distances
       
        // initialize v0 (the previous row of distances)
        // this row is A[0][i]: edit distance for an empty s
        // the distance is just the number of characters to delete from t
        var v0 = Array.iterate(0, t.length + 1)(x => x + 1)
        var v1 = new Array[Int](t.length + 1)

        for {i <- 0 until s.length} {
            // calculate v1 (current row distances) from the previous row v0

            // first element of v1 is A[i+1][0]
            //   edit distance is delete (i+1) chars from s to match empty t
            v1(0) = i + 1;

            // use formula to fill in the rest of the row
            for (j <- 0 until t.length) {
                var cost = if(s(i) == t(j)) 0 else 1;
                v1(j + 1) = minimum(v1(j) + 1, v0(j + 1) + 1, v0(j) + cost);
            }
            
            // copy v1 (current row) to v0 (previous row) for next iteration
            var tmp = v0
            v0 = v1
            v1 = tmp
        }

        v1(t.length)
    }*/

    @inline def spaceAndNotSpace(a: Any, b: Any) = {
      val isASpaceChar = a match {
        case c: Char => c.isSpaceChar
        case _ => false
      }
      val isBSpaceChar = b match {
        case c: Char => c.isSpaceChar
        case _ => false
      }
      if(isASpaceChar != isBSpaceChar) 1 else 0
    }
    
    def distance(ss: TraversableOnce[Any], tt: TraversableOnce[Any], d: (Any, Any) => Int, size: Any => Int): Int = {
        // degenerate cases
        if (ss == tt) return 0
        if (ss.isEmpty) return innerSize(tt)
        if (tt.isEmpty) return innerSize(ss)
        val s = ss.toIndexedSeq
        val t = tt.toIndexedSeq

        // create two work vectors of integer distances
       
        // initialize v0 (the previous row of distances)
        // this row is A[0][i]: edit distance for an empty s
        // the distance is just the number of characters to delete from t
        var v0 = ((ArrayBuffer[Int](0), None: Option[Any], 1) /: (0 until t.length)) {
          case ((ab, prevChar, ctr), j) =>
            val charToConsider = t(j)
            val newCtr = ctr + prevChar.map(p => spaceAndNotSpace(charToConsider, p)).getOrElse(0)
            (ab += newCtr, Some(charToConsider), newCtr + 1)
        }._1.toArray
        //println(s"ss=$ss, tt=$tt.")
        //println(s"v0=${v0.mkString(",")}")
        var v1 = new Array[Int](t.length + 1)

        var sim1: Option[Any] = None
        var delta = 0

        for {i <- 0 until s.length} {
            // calculate v1 (current row distances) from the previous row v0

            // first element of v1 is A[i+1][0]
            //   edit distance is delete (i+1) chars from s to match empty t
            val si = s(i)
            delta = delta + sim1.map(si1 => spaceAndNotSpace(si1, si)).getOrElse(0)
            v1(0) = i + 1 + delta;
            // v0(j) contains the edit distance from s(0)...s(i-1) to t(0)..t(j-1)
            for (j <- 0 until t.length) {
            // v1(j) contains the edit distance from  s(0)..s(i)   to t(0)..t(j-1)
                val tj = t(j)
                val substiCost0 = d(si, tj)
                val substiCost = if(substiCost0 == 0) { // We should add 1 more if one of the two letters is added after a whitespace/
                  if(i > 0) {
                    if(j > 0) {
                      spaceAndNotSpace(t(j-1), s(i-1))
                    } else spaceAndNotSpace(si, s(i-1))
                  } else {
                    if(j > 0) {
                      spaceAndNotSpace(tj, t(j-1))
                    } else 0
                  }
                }  else substiCost0
                var sizeTj = innerSize(tj) + (if(j > 0) spaceAndNotSpace(tj, t(j-1)) else 0)
                var sizeSi = innerSize(si) + (if(i > 0) spaceAndNotSpace(si, s(i-1)) else 0)
                v1(j + 1) = minimum(v1(j) + sizeTj, v0(j + 1) + sizeSi, v0(j) + substiCost)
             // v1(j+1) contains the edit distance from  s(0)..s(i)   to t(0)..t(j)
            }
            //println(s"v1=${v1.mkString(",")}")
            
            // copy v1 (current row) to v0 (previous row) for next iteration
            var tmp = v0
            v0 = v1
            v1 = tmp
        }
        v0(t.length)
    }
  }
}