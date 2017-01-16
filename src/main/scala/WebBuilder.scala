import scala.language.dynamics
import shapeless.{::, HList, HNil}

object Implicits {
  var debug = false
  def report[A](s: =>String)(a: =>A): A = {
    if(debug) println(s.format("[to compute]"))
    val res = a
    if(debug) println(s.format(a.toString))
    res
  }

  implicit class AugmentedReverse1[A, B](r: (A ~~> B)) {
    def apply[BA](arg1: BA ~~> A): (BA ~~> B) = {
      new (BA ~~> B) {
        def get(in: BA) = r.get(arg1.get(in))
        def put(out: B, in: Option[BA]) = {
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
        def put(out: C, in: Option[(BA, BB)]) = {
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
  
  implicit class AugmentedReverseHNil[A, B](r: ((A :: HNil) ~~> B)) {
    def apply[BA](arg1: BA ~~> A): ((BA :: HNil) ~~> B) = {
      new ((BA :: HNil) ~~> B) {
        def get(in: (BA :: HNil)) = r.get(arg1.get(in.head) :: HNil)
        def put(out: B, in: Option[(BA :: HNil)]): Iterable[(BA :: HNil)] = {
          val init_ba = in.map(_.head)
          val middle = in.map{ case init_ba :: HNil => (arg1.get(init_ba) :: HNil) }
          for{ a::b <- r.put(out, middle)
               ba <- arg1.put(a, init_ba)} yield {
            ba :: HNil
          }
        }
      }
    }
  }
  
  implicit class AugmentedReverseHCons[A, B, R <: ::[_, _]](r: ((A :: R) ~~> B)) {
    def apply[BA, BR <: ::[_, _]](arg1: BA ~~> A, arg2: BR ~~> R): ((BA :: BR) ~~> B) = {
      new ((BA :: BR) ~~> B) {
        def get(in: (BA :: BR)) = r.get(arg1.get(in.head) :: arg2.get(in.tail))
        def put(out: B, in: Option[(BA :: BR)]): Iterable[(BA :: BR)] = {
          val init_ba = in.map(_.head)
          val init_bb = in.map(_.tail)
          val middle = in.map{ case init_ba :: init_bb => (arg1.get(init_ba) :: arg2.get(init_bb)) }
          for{ a::b <- r.put(out, middle)
               ba <- arg1.put(a, init_ba)
               bb <- arg2.put(b, init_bb) } yield {
            ba :: bb
          }
        }
      }
    }
    /*def apply[BA, BR <: ::[_, _]](args: BA ~~> A, arg2: BR ~~> R): ((BA :: BR) ~~> B) = {
    
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

    def put(out: D, a: Option[A]): Iterable[A] = 
      try { r.put(out.asInstanceOf[B], a) } catch { case _: Exception => Nil }
  }
  /*implicit def generalize[A, B, C <: A, D >: B](r: A ~~> B): (C ~~> D) = new (C ~~> D) {
    def get(a: C) = r.get(a): D

    def put(a: Option[C], out: D): Iterable[C] = 
      try { r.put(a.asInstanceOf[A], out).asInstanceOf[Iterable[C]] } catch { case _: Exception => Nil }
  }*/
}

object WebBuilder {
  import WebTrees._
  
  import Implicits._
  
  
  object < extends Dynamic {
    def apply(name: String) = Const[Element](Element(name, Nil, Nil, Nil))
    val span = apply("span")
    val div = apply("div")
    val ul = apply("ul")
    val li = apply("li")
    def selectDynamic(name: String) = apply(name)
  }
}