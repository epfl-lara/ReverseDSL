import scala.language.dynamics
import shapeless.{:: => #:, HList, HNil}

object Implicits {
  var debug = false
  def report[A](s: =>String)(a: =>A): A = {
    if (debug) println(s.replaceAll("%s$", "[to compute]"))
    val res = a
    if (debug) println(s.replaceAll("%s$", a.toString.replaceAll("\\$", "\\\\\\$")))
    res
  }

  implicit class AugmentedReverse1[A, B](r: (A ~~> B)) {
    def apply[BA](arg1: BA ~~> A): (BA ~~> B) = {
      new (BA ~~> B) {
        def get(in: BA) = r.get(arg1.get(in))
        def put(out: B, in: Option[BA]) = report(s"AugmentedReverse1.put($out, $in) = %s"){
          val middle = in.map(arg1.get)
          for{ a <- r.put(out, middle)
               ba <- arg1.put(a, in)} yield { ba }
        }
      }
    }
  }
  implicit class AugmentedReverse2[A, B, C](r: ((A, B) ~~> C)) {
    def apply[BA, BB](arg1: BA ~~> A, arg2: BB ~~> B): (BA, BB) ~~> C = {
      new ((BA, BB) ~~> C) {
        def get(in: (BA, BB)) = r.get(arg1.get(in._1), arg2.get(in._2))
        def put(out: C, in: Option[(BA, BB)]) = report(s"AugmentedReverse2.put($out, $in) = %s"){
          val init_ba = in.map(_._1)
          val init_bb = in.map(_._2)
          val middle = in.map{ case (init_ba, init_bb) => (arg1.get(init_ba), arg2.get(init_bb)) }
          for{ (a, b) <- r.put(out, middle)
               ba <- arg1.put(a, init_ba)
               bb <- arg2.put(b, init_bb) } yield {
            (ba, bb)
          }
        }
      }
    }
  }
  
  implicit class AugmentedReverseHNil[A, B](r: ((A #: HNil) ~~> B)) {
    def apply[BA](arg1: BA ~~> A): ((BA #: HNil) ~~> B) = {
      new ((BA #: HNil) ~~> B) {
        def get(in: (BA #: HNil)) = r.get(arg1.get(in.head) :: HNil)
        def put(out: B, in: Option[(BA #: HNil)]): Iterable[(BA #: HNil)] = {
          val init_ba = in.map(_.head)
          val middle = in.map{ case init_ba #: HNil => (arg1.get(init_ba) :: HNil) }
          for{ a #: b <- r.put(out, middle)
               ba <- arg1.put(a, init_ba)} yield {
            ba:: HNil
          }
        }
      }
    }
  }
  
  implicit class AugmentedReverseHCons[A, B, R <: #:[_, _]](r: ((A #: R) ~~> B)) {
    def apply[BA, BR <: #:[_, _]](arg1: BA ~~> A, arg2: BR ~~> R): ((BA #: BR) ~~> B) = {
      new ((BA #: BR) ~~> B) {
        def get(in: (BA #: BR)) = r.get(arg1.get(in.head) :: arg2.get(in.tail))
        def put(out: B, in: Option[(BA #: BR)]): Iterable[(BA #: BR)] = {
          val init_ba = in.map(_.head)
          val init_bb = in.map(_.tail)
          val middle = in.map{ case init_ba #: init_bb => (arg1.get(init_ba) :: arg2.get(init_bb)) }
          for{ a #: b <- r.put(out, middle)
               ba <- arg1.put(a, init_ba)
               bb <- arg2.put(b, init_bb) } yield {
            ba :: bb
          }
        }
      }
    }
    /*def apply[BA, BR <: #:[_, _]](args: BA ~~> A, arg2: BR ~~> R): ((BA #: BR) ~~> B) = {
    
    }*/
  }
  
  implicit def RemoveUnit[A, B](r: ((Unit, A)~~>B)) = new (A ~~> B) {
    def get(a: A) = r.get(((), a))
    def put(out: B, a: Option[A]) = report(s"RemoveUnit.put($out, $a) = %s") { r.put(out, a.map(((), _))).map(_._2)}
  }
  import WebTrees._
  implicit class AugmentedConst[A](r: (A ~~> Element)) {
    def apply[B](args: B ~~> List[Tree]): ((A, B)  ~~> Element) = new  ((A, B)  ~~> Element) {
      def get(ab: (A, B)) = 
        WebElementComposition.get((r.get(ab._1), args.get(ab._2)))
      def put(out: Element, ab: Option[(A, B)]): Iterable[(A, B)] = report(s"AugmentedConst.put($out, $ab) = %s"){
        val a = ab.map(_._1)
        val b = ab.map(_._2)
        val middle = ab.map(x => (r.get(x._1), args.get(x._2)))
        for{ (rEl, argsEl) <- WebElementComposition.put(out, middle)
          puts_r = r.put(rEl, a)
          puts_args = args.put(argsEl, b)
          rA <- puts_r
          argsA <- puts_args
        } yield (rA, argsA)
      }
    }
  }
  implicit def generalize[A, B, D >: B](r: A ~~> B): (A ~~> D) = new (A ~~> D) {
    def get(a: A): D = r.get(a): D

    def put(out: D, a: Option[A]): Iterable[A] =  report(s"generalize.put($out, $a) = %s") {
      try { r.put(out.asInstanceOf[B], a) } catch { case _: Exception => Nil }
    }
  }
  
  implicit class ListProducer[A, B](a: A ~~> List[B]) {
    def filter(f: B => Boolean): (A ~~> List[B]) = {
      a andThen FilterReverse(f)
    }
    def map[C](f: B ~~> C): (A ~~> List[C]) = {
      a andThen MapReverse(f)
    }
    def map[C](f: Id[B] => (B ~~> C)): A ~~> List[C] = {
      a andThen MapReverse(f(Id[B]()))
    }
  }
  implicit class TupleProducer[A, B, C](f: A ~~> (B, C)) {
    def _1: (A ~~> B) = new (A ~~> B) {
      def get(a: A): B = f.get(a)._1
      def put(out: B, in: Option[A]) = report(s"_1.put($out, $in) = %s")  {
        in.map(f.get) match {
          case Some((b, c)) =>
            f.put((out, c), in)
          case None =>     
            Nil
        }
      }
    }
    def _2: (A ~~> C) = new (A ~~> C) {
      def get(a: A): C = f.get(a)._2
      def put(out: C, in: Option[A]) = report(s"_2.put($out, $in) = %s") {
        in.map(f.get) match {
          case Some((b, c)) =>
            f.put((b, out), in)
          case None =>     
            Nil
        }
      }
    }
  }
  implicit def removeDuplicateArgument[A, C](f: (A, A) ~~> C): (A ~~> C) = new (A ~~> C) {
    def get(a: A) = f.get((a, a))
    def put(c: C, init: Option[A]) = report(s"removeDuplicateArguments.put($c, $init) = %s") {
      val p = f.put(c, (init zip init).headOption)
      val result = p.toStream.flatMap{ case (a, b) => List(a, b) }.distinct
      // If one of the suggested a is not the one in init, init is filtered out.
      (init match {
        case Some(i) => 
          if (result.exists(_ != i)) result.filter(_ != i) else result
        case None =>
          result
      }).toList
    }
  }
  implicit def removeDuplicateArgument3[A, C](f: ((A, A), A) ~~> C): (A ~~> C) = new (A ~~> C) {
    def get(a: A) = f.get(((a, a), a))
    def put(c: C, init: Option[A]) = report(s"removeDuplicateArgument3.put($c, $init) = %s") {
      val p = f.put(c, (init zip init zip init).headOption)
      val result = p.toStream.flatMap{ case ((a, b), c) => List(a, b, c) }.distinct
      // If one of the suggested a is not the one in init, init is filtered out.
      (init match {
        case Some(i) => 
          if (result.exists(_ != i)) result.filter(_ != i) else result
        case None =>
          result
      }).toList
    }
  }
  implicit class StringProducer[A](f: (A ~~> String)) {
    /*def +[B](other: (B ~~> String)): ((A, B) ~~> String) = {
      Pair(f, other) andThen StringAppend
    }*/
    def +(other: =>(A ~~> String)): (A ~~> String) = {
      Pair(f, other) andThen StringAppend
    }
    /*def format[B](other: (B ~~> List[Any])): ((A, B) ~~> String) = {
      Pair(f, other) andThen StringFormatReverse
    }*/
    def format(other: (A ~~> List[Any])): (A ~~> String) = {
      Pair(f, other) andThen StringFormatReverse
    }
  }
  def reverselistiterable[A](l: List[Iterable[A]]): Iterable[List[A]] = report(s"reverselistiterable($l)=%s"){
    l match {
      case Nil => Stream(Nil)
      case a::b => 
        a.flatMap(fb => reverselistiterable(b).map(fb::_))
    }
  }
  
  def intersect[A](l: List[Iterable[A]]): Stream[A] = report(s"intersect(${l.map(_.toList)}) = %s"){
    l match {
      case Nil => Stream.empty
      case head::Nil => head.toStream
      case head::tail => if (l.exists(_.isEmpty)) Stream.empty else {
        val e = head.head
        if (l.forall(x => x.exists(f => f == e))) {
          e #:: {
            intersect(l.map(ll => ll.filter(_ != e)))
          }
        } else {
          intersect(l.map(ll => ll.filter(_ != e)))
        }
      }
    }
  }
  
  /** All elements not equal to origin which do not appear everywhere.*/
  def intersectLight[A](l: List[Iterable[A]], orig: A, first: Boolean = true): Stream[A] = report(s"intersectLight(${l.map(_.toList)}, $orig) = %s"){
    l match {
      case Nil => Stream.empty
      case Nil::tail => intersectLight(tail, orig, false)
      case head::tail =>
        val headhead = head.head      
        if (headhead == orig)
        intersectLight(head.tail::tail, orig, first)
        else if(!first || tail.exists(i => i.forall(e => e != headhead))) {
          headhead #:: intersectLight(l.map(ll => ll.filter(_ != headhead)), orig, first)
        } else { // It was already taken into account in intersect.
          intersectLight(l.map(ll => ll.filter(_ != headhead)), orig, first)
        }
    }
  }
  
  /*implicit def listOfTransformToTransformOfList[A, B](a: List[A ~~> B]): (List[A] ~~> List[B]) = new (List[A] ~~> List[B]) {
    def get(in: List[A]) = a.zip(in).map{ case (ela, i) => ela.get(i) }
    
    def put(out: List[B], in1: Option[List[A]]): Iterable[List[A]] = {
      val in1l = in1 match { case None => out.map(_ => None: Option[A]) case Some(l) => l.map(Some(_): Option[A]) }
      val iterables = out.zip(in1l).zip(a) map {
        case ((o, i), a) => a.put(o, i)
      }
      reverselistiterable(iterables)
    }
  }*/
  implicit def listOfTransformToTransformOfList[A, B](a: List[A ~~> B]): (A ~~> List[B]) = new (A ~~> List[B]) {
    def get(i: A) = a.map{ case ela => ela.get(i) }
    
    def put(out: List[B], in1: Option[A]): Iterable[A] = report(s"listOfTransformToTransformOfList.put($out, $in1) = %s"){
      val argForIntersect: List[Iterable[A]] = a.zip(out).map{ case (ela, o) => ela.put(o, in1) }
      val res = intersect(argForIntersect)
      res #::: in1.map(aEl => intersectLight(argForIntersect, aEl)).getOrElse(Stream.empty)
    }
  } 
  
  def Listfill[B, C](n: C ~~> (Int, B)) = new (C ~~> List[B]) {
    def get(c: C): List[B] = {
      val (i, b) = n.get(c)
      List.fill(i)(b)
    }
    def put(out: List[B], in: Option[C]) = {
      (in map n.get) match {
        case Some((i, b)) =>
          if (out.forall(e => e == b)) {
            n.put((out.length, b), in)
          } else {
            val newCandidates = out.filter(e => e != b).distinct.toStream
            for{ possibleOut <- newCandidates
                 cInput <- n.put((out.length, possibleOut), in)
            } yield cInput
          }
        case None => // No hint on the initial output.
          for{ possibleOut <- out.distinct.toStream
               cInput <- n.put((out.length, possibleOut), in)
          } yield cInput
      }
    }
  }
  
  /*implicit def generalize[A, B, C <: A, D >: B](r: A ~~> B): (C ~~> D) = new (C ~~> D) {
    def get(a: C) = r.get(a): D

    def put(a: Option[C], out: D): Iterable[C] = 
      try { r.put(a.asInstanceOf[A], out).asInstanceOf[Iterable[C]] } catch { case _: Exception => Nil }
  }*/
}