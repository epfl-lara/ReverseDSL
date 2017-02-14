import scala.language.dynamics
import shapeless.{HList, HNil, :: => #:}

import scala.language.implicitConversions

object Implicits {
  import ImplicitTuples._
  import inox._
  import inox.trees._
  import inox.trees.dsl._

  var debug = false
  var indentation = 0
  def report[A](s: =>String, force: Boolean = false)(a: =>A): A = {
    if (debug || force) println((" " * indentation) + s.replaceAll("%s$", "[to compute]"))
    indentation += 1
    val res = try {
      a
    } catch {
      case e: Exception =>
      indentation -= 1
      println((" " * indentation) + s.replaceAll("%s$", "[was computing]"))
      throw e
    }
    indentation -= 1
    if (debug || force) println((" " * indentation) + s.replaceAll("%s$", a.toString.replaceAll("\\$", "\\\\\\$")))
    res
  }

/*
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
  
  implicit def removeDuplicateArgument[A, C](f: (A, A) ~~> C): (A ~~> C) = new (A ~~> C) {
    def get(a: A) = f.get((a, a))
    def put(c: C, init: Option[A]) = report(s"removeDuplicateArguments.put($c, $init) = %s") {
      val p = f.put(c, (init zip init).headOption)
      val result: Stream[A] = p.toStream.flatMap{
        case (a, b) => RecomposeTuples.unapply((a, b))
      }.distinct
      if(debug) println((" "*indentation) + " result:"+result/*.take(2)*/.toList)
      
      val result2 = init match {
        case Some(i) => 
          if (result.exists(_ != i)) result.filter(_ != i) else result
        case None =>
          result
      }
      
      if(debug) println((" "*indentation) +  " result2:"+result2.toList/*.take(2)*/)
      
      def reorderStreamWorkingFirst(s: Stream[A]): Stream[A] = {
        val head = s.take(3)
        val tail = s.drop(3)
        head.filter(x => get(x) == c) #::: head.filterNot(x => get(x) == c) #::: tail
        //s
      }
      // If one of the suggested a is not the one in init, init is filtered out.
      val realresult =
      reorderStreamWorkingFirst(result2).distinct.toList
      
      if(debug) println((" "*indentation) +  " realResult:"+realresult/*.take(2)*/)
      realresult
    }
  }
  
  implicit def removeDuplicateArgument3[A, C](f: (A, A, A) ~~> C): (A ~~> C) = new (A ~~> C) {
    def get(a: A) = f.get((a, a, a))
    def put(c: C, init: Option[A]) = report(s"removeDuplicateArguments3.put($c, $init) = %s") {
      val p = f.put(c, (init map { x => (x, x, x) }).headOption)
      val result: Stream[A] = p.toStream.flatMap{
        case (a, b, c) => RecomposeTuples.unapply3((a, b, c))
      }.distinct
      if(debug) println((" "*indentation) + " result:"+result/*.take(2)*/.toList)
      
      val result2 = init match {
        case Some(i) => 
          if (result.exists(_ != i)) result.filter(_ != i) else result
        case None =>
          result
      }
      
      if(debug) println((" "*indentation) +  " result2:"+result2.toList/*.take(2)*/)
      
      def reorderStreamWorkingFirst(s: Stream[A]): Stream[A] = {
        /*val head = s.take(3)
        val tail = s.drop(3)
        head.filter(x => get(x) == c) #::: head.filterNot(x => get(x) == c) #::: tail*/
        s
      }
      // If one of the suggested a is not the one in init, init is filtered out.
      val realresult =
      reorderStreamWorkingFirst(result2).distinct.toList
      
      if(debug) println((" "*indentation) +  " realResult:"+realresult/*.take(2)*/)
      realresult
    }
  }
  /*implicit def removeDuplicateArgument3[A, C](f: ((A, A), A) ~~> C): (A ~~> C) = new (A ~~> C) {
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
  }*/
  
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
    
    def ++(f: A ~~> List[B]): (A ~~> List[B]) = new ((A, A) ~~> List[B]) {
      def get(in: (A, A)) = a.get(in._1) ++ f.get(in._2)
      def put(out: List[B], in: Option[(A, A)]) = report(s"++.put($out, $in) = %s") {
        (in map (x => (a.get(x._1), f.get(x._2)))) match {
          case None => for{ in1 <- a.put(out, in.map(_._1)); in2 <- f.put(out, in.map(_._1)) } yield (in1, in2)
          case Some((initOut1, initOut2)) =>
              if (initOut1 ++ initOut2 == out) in.toList
              else {
                val keepFirstIntact: Iterable[(A, A)] = (if(out.length >= initOut1.length) f.put(out.drop(initOut1.length), in.map(_._2)).map((in.get._1, _: A)) else Nil)
                val keepSecondIntact: Iterable[(A, A)] = (if(out.length >= initOut2.length) a.put(out.take(out.length - initOut2.length), in.map(_._1)).map((_: A, in.get._2)) else Nil)
                /*val modifyBoth: Iterable[(A, A)] = for{(kFirst1, kFirst2) <- keepFirstIntact
                  (kSecond1, kSecond2) <- keepSecondIntact
                } yield (kSecond1, kFirst2)*/
                val parsing: Iterable[(A, A)] = for{i <- (0 until out.length).reverse.toIterable
                  (start, end) = out.splitAt(i)
                  aputs = a.put(start, in.map(_._1))
                  fputs = f.put(end,   in.map(_._2))
                  //_ = println(s"split:$i, out=${(start, end)}\naputs: ${aputs.mkString(",")}\nfputs: ${fputs.mkString(",")}")
                  astart <- aputs
                  fend <- fputs
                } yield (astart, fend)
                // List(1, 2), List(1)
                //println("KeepFirstIntact:" + keepFirstIntact.toList.mkString(","))
                //println("keepSecondIntact:" + keepSecondIntact.toList.mkString(","))
                (keepFirstIntact ++ keepSecondIntact/* ++ modifyBoth*/ ++ parsing).filter(res => {
                  //println(s"? get($res) -> ${get(res)}")
                  if(get(res) == out) {
                    //println("True: " + out)
                    true
                  } else {
                    //println("false: Expecting " + out)
                    false
                  }
                })
              }
        }
      }
    }
    /*def headOption = new (A ~~> Option[B]) {
      def get(in: A) = a.get(in).headOption
      def put(out: Option[B], in: Option[A]) = {
        in match {
          case None => out.toList
        }
      }
    }*/
  }
  implicit class RegexEnhancer(e: scala.util.matching.Regex) {
    def replaceAllIn[I](s: I ~~> String, f: List[String] ~~> String): (I ~~> String) = 
      s andThen RegexReplaceAllInReverse(e, f)
  }
  */
  implicit class StringProducer[A: Constrainable](f: (A ~~> String)) {
    /*def +[B](other: (B ~~> String)): ((A, B) ~~> String) = {
      Pair(f, other) andThen StringAppend
    }*/
    def +(other: (A ~~> String)): (A ~~> String) = {
      PairSame(f, other) andThen StringAppendReverse
    }
    /*def format[B](other: (B ~~> List[Any])): ((A, B) ~~> String) = {
      Pair(f, other) andThen StringFormatReverse
    }*/
    /*def format(other: (A ~~> List[Any])): (A ~~> String) = {
      Pair(f, other) andThen StringFormatReverse
    }
    
    def length = new (A ~~> Int) {
      def get(in: A) = f.get(in).length
      def put(out: Int, in1: Option[A]) = {
        in1 match {
          case Some(a) =>
            val s = f.get(a)
            if(s.length == out) List(a) else {
              f.put((s * ((out + s.length - 1) / s.length)).take(out), in1)
            }
          case None => f.put("?" * out, in1)
        }
      }
    }
    
    def substring(start: Int, end: Int) = new (A ~~> String) {
      def get(in: A) = f.get(in).substring(start, end)
      def put(out: String, in1: Option[A]) = {
        (in1 map f.get) match {
          case None => f.put(" " * start + out, None)
          case Some(s) => f.put(s.substring(0, start) + out + s.substring(end), in1)
        }
      }
    }

    def substring(start: (A ~~> Int), end: (A ~~> Int)): (A ~~> String) = new ((A, A, A) ~~> String) {
      def get(in: (A, A, A)) = f.get(in._1).substring(start.get(in._2), end.get(in._3))
      def put(out: String, in1: Option[(A, A, A)]) = report("substring.put($out, $in1) %s") {
        in1 match {
          case Some((a1, a2, a3)) =>
            val s = f.get(a1)
            val b = start.get(a2)
            val e = end.get(a3)
            val newStart = b
            val newEnd = b + out.length
            val startA = start.put(newStart, in1.map(_._2))
            val endA = end.put(newEnd, in1.map(_._3))
            val fputs = f.put(s.substring(0, b) + out + s.substring(e), in1.map(_._1))
            for{x <- fputs;
                y <- startA;
                z <- endA
            } yield (x, y, z)
          case None =>
            //f.put(" " * start + out, None)
            Nil
        }
      }
    }
    
    def indexOfSlice(substring: String) = new (A ~~> Int) {
      def get(a: A) = f.get(a).indexOfSlice(substring)
      def put(out: Int, in1: Option[A]) = in1 match {
        case None => Nil
        case Some(a) =>
          val s = f.get(a)
          val i = s.indexOfSlice(substring)
          if(i == out) List(a)
          else if(i == -1) { // The substring was not there before. Return all the possible insertions.
            for{i <- (0 to s.length).toStream
                (k1, k2) = s.splitAt(i)
                c = k1+substring+k2
                sol <- f.put(c, in1)
            } yield sol
            
          } else {
            if (out == -1) { // The substring should disappear.
              f.put(s.take(i) + s.drop(i+substring.length), in1)
            } else if(out >= 0 && out <= s.length - substring.length) { // Move the substring in the original string so that the index is the right one.
              // Caution: May not be ok if appears multiple times.
              val previousS = s.take(i) + s.drop(i+substring.length)
              val (k1, k2) = previousS.splitAt(out)
              
              f.put(k1 + substring + k2, in1)
            } else {
              Nil
            }
          }
      }
    }
    
    def indexOfSlice(substring: A ~~> String): (A ~~> Int) = new ((A, A) ~~> Int) {
      def get(a: (A, A)) = f.get(a._1).indexOfSlice(substring.get(a._2))
      def put(out: Int, in1: Option[(A, A)]) = in1 match {
        case None => Nil
        case Some(a@(a1, a2)) =>
          val s = f.get(a1)
          val sub = substring.get(a2)
          val i = s.indexOfSlice(sub)
          val subput = substring.put(sub, in1.map(_._2))
          if(i == out) List(a)
          else if(i == -1) { // The substring was not there before. Return all the possible insertions.
            for{
                i <- (0 to s.length).toStream
                (k1, k2) = s.splitAt(i)
                c = k1+sub+k2
                m1 <- f.put(c, in1.map(_._1))
                m2 <- subput
            } yield (m1, m2)
          } else {
            if (out == -1) { // The substring should disappear.
              val fput = f.put(s.take(i) + s.drop(i+sub.length), in1.map(_._1))
              for{m1 <- fput
                  m2 <- subput} yield (m1, m2)
            } else if(out >= 0 && out <= s.length - sub.length) { // Move the substring in the original string so that the index is the right one.
              // Caution: May not be ok if appears multiple times.
              val previousS = s.take(i) + s.drop(i+sub.length)
              val (k1, k2) = previousS.splitAt(out)
              val fput = f.put(k1 + sub + k2, in1.map(_._1))
              (for{
                  m1 <- fput
                  m2 <- subput
              } yield (m1, m2)) ++ {
                val maybe = s.substring(out)
                val originalf = f.put(s, in1.map(_._1))
                for{ i <- (1 to maybe.length).toStream
                     prefix = maybe.substring(0, i)
                     outpossible = s.indexOfSlice(prefix)
                     if outpossible == out
                     m1 <- originalf
                     m2 <- substring.put(prefix, in1.map(_._2))
                } yield {
                  (m1, m2)
                }
              }
            } else {
              Nil
            }
          }
      }
    }*/
  }
  /*
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
  */
}