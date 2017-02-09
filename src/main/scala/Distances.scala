

object Distances {
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
  }
  
  def innerSize(a: Any): Int = a match {
    case a: Char => 1
    case s: collection.immutable.StringOps => s.length
    case e => size(a)
  }

  def distance(a: Any, b: Any): Int = {
    if (a == b) 0 else {
      (a, b) match {
        case (a: Char, b: Char) => 1
        case (a: String, b: String) => Levenshtein.distance(a, b, distance, size)
        case (a: TraversableOnce[_], b: TraversableOnce[_]) => Levenshtein.distance(a, b, distance, size)
        case (a: Product, b: Product) =>
          if (a.getClass == b.getClass) {
            (0 /: (0 until a.productArity)) {
              case (s, i) => s + distance(a.productElement(i), b.productElement(i))
            }
          } else {
            size(a) + size(b) // remove a and write b
          }
        case (true, false) => 4
        case (false, true) => 4
        case (a: Int, b: Int) =>
          distance(a.toString, b.toString)
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
        var v0 = Array.iterate(0, t.length + 1)(x => x + 1)
        //println(s"ss=$ss, tt=$tt.")
        //println(s"v0=${v0.mkString(",")}")
        var v1 = new Array[Int](t.length + 1)

        for {i <- 0 until s.length} {
            // calculate v1 (current row distances) from the previous row v0

            // first element of v1 is A[i+1][0]
            //   edit distance is delete (i+1) chars from s to match empty t
            v1(0) = i + 1;
            val si = s(i)
            // use formula to fill in the rest of the row
            for (j <- 0 until t.length) {
                val tj = t(j)
                var substiCost = d(si, tj)
                var insertCost = innerSize(tj)
                var deleteCost = innerSize(si)
                v1(j + 1) = minimum(v1(j) + insertCost, v0(j + 1) + deleteCost, v0(j) + substiCost)
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