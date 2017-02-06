

trait ImplicitTuples {
  object RecomposeTuples {
    def unapply[A](t: (A, A)): List[A] = {
      val a = t._1
      val b = t._2
      t match {
        /*case ((a1, a2, a3, a4),
              (b1, b2, b3, b4)) => List(a, b,
              (a1, a2, a3, b4).asInstanceOf[A],
              (a1, a2, b3, b4).asInstanceOf[A],
              (a1, b2, b3, b4).asInstanceOf[A]
              )  : List[A]*/
        case ((a1, a2, a3),
              (b1, b2, b3)) => List(a, b,
              (a1, a2, b3).asInstanceOf[A],
              (a1, b2, b3).asInstanceOf[A])  : List[A]
        case ((a1, a2),
              (b1, b2)) => List(a, b,
              (a1, b2).asInstanceOf[A])  : List[A]
        case _ => List(a, b)
      }
    }
    def unapply3[A](t: (A, A, A)): List[A] = {
      val a = t._1
      val b = t._2
      val c = t._3
      t match {
        case ((a1, a2, a3),
              (b1, b2, b3),
              (c1, c2, c3)) => List(
              (a1, b2, c3).asInstanceOf[A],
              a, b, c)  : List[A]
        case ((a1, a2),
              (b1, b2),
              (c1, c2)) => List(a, b,
              (a1, b2).asInstanceOf[A],
              (a1, c2).asInstanceOf[A],
              (b1, c2).asInstanceOf[A])  : List[A]
        case _ => List(a, b, c)
      }
    }
  }
  
  class TupleProducer[A, Tuple, C](
      val f: A ~~> Tuple, val get0: Tuple => C, val put0: ((Tuple, C)) => Tuple, val index: Int)
    extends (A ~~> C) {
    def get(in: A): C = get0(f.get(in))
    def put(out: C, in1: Option[A]): Iterable[A] = Implicits.report(s"_$index.put($out, $in1) = %s")  {
      in1.map(f.get) match {
        case Some(outOrig) =>
          f.put(put0(outOrig, out), in1)
        case None => Nil
      }
    }
  }
  
  implicit class Tuple2Producer[A, B1, B2]
                        (f: A ~~> (B1, B2)) {
    def _1 = new TupleProducer[A, (B1, B2), B1](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2), B2](f, _._2, x => x._1.copy(_2 = x._2), 2)
  }
  implicit class Tuple3Producer[A, B1, B2, B3]
                        (f: A ~~> (B1, B2, B3)) {
    def _1 = new TupleProducer[A, (B1, B2, B3), B1](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3), B2](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3), B3](f, _._3, x => x._1.copy(_3 = x._2), 3)
  }
  implicit class Tuple4Producer[A, B1, B2, B3, B4]
                        (f: A ~~> (B1, B2, B3, B4)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4), B1](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4), B2](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4), B3](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4), B4](f, _._4, x => x._1.copy(_4 = x._2), 4)
  }
  implicit class Tuple5Producer[A, B1, B2, B3, B4, B5]
                        (f: A ~~> (B1, B2, B3, B4, B5)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5), B1](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5), B2](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5), B3](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5), B4](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5), B5](f, _._5, x => x._1.copy(_5 = x._2), 5)
  }
  implicit class Tuple6Producer[A, B1, B2, B3, B4, B5, B6]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6), B1](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6), B2](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6), B3](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6), B4](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6), B5](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6), B6](f, _._6, x => x._1.copy(_6 = x._2), 6)
  }
  implicit class Tuple7Producer[A, B1, B2, B3, B4, B5, B6, B7]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7), B1](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7), B2](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7), B3](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7), B4](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7), B5](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7), B6](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7), B7](f, _._7, x => x._1.copy(_7 = x._2), 7)
  }
  implicit class Tuple8Producer[A, B1, B2, B3, B4, B5, B6, B7, B8]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B1](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B2](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B3](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B4](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B5](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B6](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B7](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8), B8](f, _._8, x => x._1.copy(_8 = x._2), 8)
  }
  implicit class Tuple9Producer[A, B1, B2, B3, B4, B5, B6, B7, B8, B9]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B1](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B2](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B3](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B4](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B5](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B6](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B7](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B8](f, _._8, x => x._1.copy(_8 = x._2), 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9), B9](f, _._9, x => x._1.copy(_9 = x._2), 9)
  }
  implicit class Tuple10roducer[A, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B1 ](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B2 ](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B3 ](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B4 ](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B5 ](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B6 ](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B7 ](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B8 ](f, _._8, x => x._1.copy(_8 = x._2), 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B9 ](f, _._9, x => x._1.copy(_9 = x._2), 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10), B10](f, _._10,x => x._1.copy(_10= x._2),10)
  }
  implicit class Tuple11roducer[A, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B1 ](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B2 ](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B3 ](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B4 ](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B5 ](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B6 ](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B7 ](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B8 ](f, _._8, x => x._1.copy(_8 = x._2), 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B9 ](f, _._9, x => x._1.copy(_9 = x._2), 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B10](f, _._10,x => x._1.copy(_10= x._2),10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11), B11](f, _._11,x => x._1.copy(_11= x._2),11)
  }
  implicit class Tuple12roducer[A, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B1 ](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B2 ](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B3 ](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B4 ](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B5 ](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B6 ](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B7 ](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B8 ](f, _._8, x => x._1.copy(_8 = x._2), 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B9 ](f, _._9, x => x._1.copy(_9 = x._2), 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B10](f, _._10,x => x._1.copy(_10= x._2),10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B11](f, _._11,x => x._1.copy(_11= x._2),11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12), B12](f, _._12,x => x._1.copy(_12= x._2),12)
  }
  implicit class Tuple13roducer[A, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B1 ](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B2 ](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B3 ](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B4 ](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B5 ](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B6 ](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B7 ](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B8 ](f, _._8, x => x._1.copy(_8 = x._2), 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B9 ](f, _._9, x => x._1.copy(_9 = x._2), 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B10](f, _._10,x => x._1.copy(_10= x._2),10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B11](f, _._11,x => x._1.copy(_11= x._2),11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B12](f, _._12,x => x._1.copy(_12= x._2),12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13), B13](f, _._13,x => x._1.copy(_13= x._2),13)
  }
  implicit class Tuple14roducer[A, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B1 ](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B2 ](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B3 ](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B4 ](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B5 ](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B6 ](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B7 ](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B8 ](f, _._8, x => x._1.copy(_8 = x._2), 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B9 ](f, _._9, x => x._1.copy(_9 = x._2), 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B10](f, _._10,x => x._1.copy(_10= x._2),10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B11](f, _._11,x => x._1.copy(_11= x._2),11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B12](f, _._12,x => x._1.copy(_12= x._2),12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B13](f, _._13,x => x._1.copy(_13= x._2),13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14), B14](f, _._14,x => x._1.copy(_14= x._2),14)
  }
  implicit class Tuple15roducer[A, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B1 ](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B2 ](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B3 ](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B4 ](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B5 ](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B6 ](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B7 ](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B8 ](f, _._8, x => x._1.copy(_8 = x._2), 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B9 ](f, _._9, x => x._1.copy(_9 = x._2), 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B10](f, _._10,x => x._1.copy(_10= x._2),10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B11](f, _._11,x => x._1.copy(_11= x._2),11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B12](f, _._12,x => x._1.copy(_12= x._2),12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B13](f, _._13,x => x._1.copy(_13= x._2),13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B14](f, _._14,x => x._1.copy(_14= x._2),14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15), B15](f, _._15,x => x._1.copy(_15= x._2),15)
  }
  implicit class Tuple16roducer[A, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B1 ](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B2 ](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B3 ](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B4 ](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B5 ](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B6 ](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B7 ](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B8 ](f, _._8, x => x._1.copy(_8 = x._2), 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B9 ](f, _._9, x => x._1.copy(_9 = x._2), 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B10](f, _._10,x => x._1.copy(_10= x._2),10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B11](f, _._11,x => x._1.copy(_11= x._2),11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B12](f, _._12,x => x._1.copy(_12= x._2),12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B13](f, _._13,x => x._1.copy(_13= x._2),13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B14](f, _._14,x => x._1.copy(_14= x._2),14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B15](f, _._15,x => x._1.copy(_15= x._2),15)
    def _16= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16), B16](f, _._16,x => x._1.copy(_16= x._2),16)
  }
  implicit class Tuple17roducer[A, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B1 ](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B2 ](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B3 ](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B4 ](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B5 ](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B6 ](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B7 ](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B8 ](f, _._8, x => x._1.copy(_8 = x._2), 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B9 ](f, _._9, x => x._1.copy(_9 = x._2), 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B10](f, _._10,x => x._1.copy(_10= x._2),10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B11](f, _._11,x => x._1.copy(_11= x._2),11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B12](f, _._12,x => x._1.copy(_12= x._2),12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B13](f, _._13,x => x._1.copy(_13= x._2),13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B14](f, _._14,x => x._1.copy(_14= x._2),14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B15](f, _._15,x => x._1.copy(_15= x._2),15)
    def _16= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B16](f, _._16,x => x._1.copy(_16= x._2),16)
    def _17= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17), B17](f, _._17,x => x._1.copy(_17= x._2),17)
  }
  implicit class Tuple18roducer[A, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B1 ](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B2 ](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B3 ](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B4 ](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B5 ](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B6 ](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B7 ](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B8 ](f, _._8, x => x._1.copy(_8 = x._2), 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B9 ](f, _._9, x => x._1.copy(_9 = x._2), 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B10](f, _._10,x => x._1.copy(_10= x._2),10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B11](f, _._11,x => x._1.copy(_11= x._2),11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B12](f, _._12,x => x._1.copy(_12= x._2),12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B13](f, _._13,x => x._1.copy(_13= x._2),13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B14](f, _._14,x => x._1.copy(_14= x._2),14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B15](f, _._15,x => x._1.copy(_15= x._2),15)
    def _16= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B16](f, _._16,x => x._1.copy(_16= x._2),16)
    def _17= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B17](f, _._17,x => x._1.copy(_17= x._2),17)
    def _18= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18), B18](f, _._18,x => x._1.copy(_18= x._2),18)
  }
  implicit class Tuple19roducer[A, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B1 ](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B2 ](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B3 ](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B4 ](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B5 ](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B6 ](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B7 ](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B8 ](f, _._8, x => x._1.copy(_8 = x._2), 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B9 ](f, _._9, x => x._1.copy(_9 = x._2), 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B10](f, _._10,x => x._1.copy(_10= x._2),10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B11](f, _._11,x => x._1.copy(_11= x._2),11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B12](f, _._12,x => x._1.copy(_12= x._2),12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B13](f, _._13,x => x._1.copy(_13= x._2),13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B14](f, _._14,x => x._1.copy(_14= x._2),14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B15](f, _._15,x => x._1.copy(_15= x._2),15)
    def _16= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B16](f, _._16,x => x._1.copy(_16= x._2),16)
    def _17= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B17](f, _._17,x => x._1.copy(_17= x._2),17)
    def _18= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B18](f, _._18,x => x._1.copy(_18= x._2),18)
    def _19= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19), B19](f, _._19,x => x._1.copy(_19= x._2),19)
  }
  implicit class Tuple20roducer[A, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B1 ](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B2 ](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B3 ](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B4 ](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B5 ](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B6 ](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B7 ](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B8 ](f, _._8, x => x._1.copy(_8 = x._2), 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B9 ](f, _._9, x => x._1.copy(_9 = x._2), 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B10](f, _._10,x => x._1.copy(_10= x._2),10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B11](f, _._11,x => x._1.copy(_11= x._2),11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B12](f, _._12,x => x._1.copy(_12= x._2),12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B13](f, _._13,x => x._1.copy(_13= x._2),13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B14](f, _._14,x => x._1.copy(_14= x._2),14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B15](f, _._15,x => x._1.copy(_15= x._2),15)
    def _16= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B16](f, _._16,x => x._1.copy(_16= x._2),16)
    def _17= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B17](f, _._17,x => x._1.copy(_17= x._2),17)
    def _18= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B18](f, _._18,x => x._1.copy(_18= x._2),18)
    def _19= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B19](f, _._19,x => x._1.copy(_19= x._2),19)
    def _20= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20), B20](f, _._20,x => x._1.copy(_20= x._2),20)
  }
  implicit class Tuple21roducer[A, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B1 ](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B2 ](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B3 ](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B4 ](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B5 ](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B6 ](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B7 ](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B8 ](f, _._8, x => x._1.copy(_8 = x._2), 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B9 ](f, _._9, x => x._1.copy(_9 = x._2), 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B10](f, _._10,x => x._1.copy(_10= x._2),10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B11](f, _._11,x => x._1.copy(_11= x._2),11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B12](f, _._12,x => x._1.copy(_12= x._2),12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B13](f, _._13,x => x._1.copy(_13= x._2),13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B14](f, _._14,x => x._1.copy(_14= x._2),14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B15](f, _._15,x => x._1.copy(_15= x._2),15)
    def _16= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B16](f, _._16,x => x._1.copy(_16= x._2),16)
    def _17= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B17](f, _._17,x => x._1.copy(_17= x._2),17)
    def _18= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B18](f, _._18,x => x._1.copy(_18= x._2),18)
    def _19= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B19](f, _._19,x => x._1.copy(_19= x._2),19)
    def _20= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B20](f, _._20,x => x._1.copy(_20= x._2),20)
    def _21= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21), B21](f, _._21,x => x._1.copy(_21= x._2),21)
  }
  implicit class Tuple22roducer[A, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22]
                        (f: A ~~> (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22)) {
    def _1 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B1 ](f, _._1, x => x._1.copy(_1 = x._2), 1)
    def _2 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B2 ](f, _._2, x => x._1.copy(_2 = x._2), 2)
    def _3 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B3 ](f, _._3, x => x._1.copy(_3 = x._2), 3)
    def _4 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B4 ](f, _._4, x => x._1.copy(_4 = x._2), 4)
    def _5 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B5 ](f, _._5, x => x._1.copy(_5 = x._2), 5)
    def _6 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B6 ](f, _._6, x => x._1.copy(_6 = x._2), 6)
    def _7 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B7 ](f, _._7, x => x._1.copy(_7 = x._2), 7)
    def _8 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B8 ](f, _._8, x => x._1.copy(_8 = x._2), 8)
    def _9 = new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B9 ](f, _._9, x => x._1.copy(_9 = x._2), 9)
    def _10= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B10](f, _._10,x => x._1.copy(_10= x._2),10)
    def _11= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B11](f, _._11,x => x._1.copy(_11= x._2),11)
    def _12= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B12](f, _._12,x => x._1.copy(_12= x._2),12)
    def _13= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B13](f, _._13,x => x._1.copy(_13= x._2),13)
    def _14= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B14](f, _._14,x => x._1.copy(_14= x._2),14)
    def _15= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B15](f, _._15,x => x._1.copy(_15= x._2),15)
    def _16= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B16](f, _._16,x => x._1.copy(_16= x._2),16)
    def _17= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B17](f, _._17,x => x._1.copy(_17= x._2),17)
    def _18= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B18](f, _._18,x => x._1.copy(_18= x._2),18)
    def _19= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B19](f, _._19,x => x._1.copy(_19= x._2),19)
    def _20= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B20](f, _._20,x => x._1.copy(_20= x._2),20)
    def _21= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B21](f, _._21,x => x._1.copy(_21= x._2),21)
    def _22= new TupleProducer[A, (B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22), B22](f, _._22,x => x._1.copy(_22= x._2),22)
  }
}