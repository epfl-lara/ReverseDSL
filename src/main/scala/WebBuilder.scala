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
        def perform(in: BA) = r.perform(arg1.perform(in))
        def unperform(in: Option[BA], out: B) = {
          val middle = in.map(arg1.perform)
          for{ a <- r.unperform(middle, out)
               ba <- arg1.unperform(in, a)} yield { ba }
        }
      }
    }
  }
  implicit class AugmentedReverse2[A, B, C](r: ((A, B) ~~> C)) {
    def apply[BA, BB](arg1: BA ~~> A, arg2: BB ~~> B): (BA, BB) ~~> C = {
      new ((BA, BB) ~~> C) {
        def perform(in: (BA, BB)) = r.perform(arg1.perform(in._1), arg2.perform(in._2))
        def unperform(in: Option[(BA, BB)], out: C) = {
          val init_ba = in.map(_._1)
          val init_bb = in.map(_._2)
          val middle = in.map{ case (init_ba, init_bb) => (arg1.perform(init_ba), arg2.perform(init_bb)) }
          for{ (a, b) <- r.unperform(middle, out)
               ba <- arg1.unperform(init_ba, a)
               bb <- arg2.unperform(init_bb, b) } yield {
            (ba, bb)
          }
        }
      }
    }
  }
  
  implicit class AugmentedReverseHNil[A, B](r: ((A :: HNil) ~~> B)) {
    def apply[BA](arg1: BA ~~> A): ((BA :: HNil) ~~> B) = {
      new ((BA :: HNil) ~~> B) {
        def perform(in: (BA :: HNil)) = r.perform(arg1.perform(in.head) :: HNil)
        def unperform(in: Option[(BA :: HNil)], out: B): Iterable[(BA :: HNil)] = {
          val init_ba = in.map(_.head)
          val middle = in.map{ case init_ba :: HNil => (arg1.perform(init_ba) :: HNil) }
          for{ a::b <- r.unperform(middle, out)
               ba <- arg1.unperform(init_ba, a)} yield {
            ba :: HNil
          }
        }
      }
    }
  }
  
  implicit class AugmentedReverseHCons[A, B, R <: ::[_, _]](r: ((A :: R) ~~> B)) {
    def apply[BA, BR <: ::[_, _]](arg1: BA ~~> A, arg2: BR ~~> R): ((BA :: BR) ~~> B) = {
      new ((BA :: BR) ~~> B) {
        def perform(in: (BA :: BR)) = r.perform(arg1.perform(in.head) :: arg2.perform(in.tail))
        def unperform(in: Option[(BA :: BR)], out: B): Iterable[(BA :: BR)] = {
          val init_ba = in.map(_.head)
          val init_bb = in.map(_.tail)
          val middle = in.map{ case init_ba :: init_bb => (arg1.perform(init_ba) :: arg2.perform(init_bb)) }
          for{ a::b <- r.unperform(middle, out)
               ba <- arg1.unperform(init_ba, a)
               bb <- arg2.unperform(init_bb, b) } yield {
            ba :: bb
          }
        }
      }
    }
    /*def apply[BA, BR <: ::[_, _]](args: BA ~~> A, arg2: BR ~~> R): ((BA :: BR) ~~> B) = {
    
    }*/
  }
  
  implicit def RemoveUnit[A, B](r: ((Unit, A)~~>B)) = new (A ~~> B) {
    def perform(a: A) = r.perform(((), a))
    def unperform(a: Option[A], out: B) = report(s"RemoveUnit.unperform($a, $out) = %s") { r.unperform(a.map(((), _)), out).map(_._2)}
  }
  import WebTrees._
  implicit class AugmentedConst[A](r: (A ~~> Element)) {
    def apply[B](args: B ~~> List[Tree]): ((A, B)  ~~> Element) = new  ((A, B)  ~~> Element) {
      def perform(ab: (A, B)) = 
        WebElementComposition.perform((r.perform(ab._1), args.perform(ab._2)))
      def unperform(ab: Option[(A, B)], out: Element): Iterable[(A, B)] = report(s"AugmentedConst.unperform($ab, $out) = %s"){
        val a = ab.map(_._1)
        val b = ab.map(_._2)
        val middle = ab.map(x => (r.perform(x._1), args.perform(x._2)))
        for{ (rEl, argsEl) <- WebElementComposition.unperform(middle, out)
          unperforms_r = r.unperform(a, rEl)
          unperforms_args = args.unperform(b, argsEl)
          rA <- unperforms_r
          argsA <- unperforms_args
        } yield (rA, argsA)
      }
    }
  }
  implicit def generalize[A, B, D >: B](r: A ~~> B): (A ~~> D) = new (A ~~> D) {
    def perform(a: A): D = r.perform(a): D

    def unperform(a: Option[A], out: D): Iterable[A] = 
      try { r.unperform(a, out.asInstanceOf[B]) } catch { case _: Exception => Nil }
  }
  /*implicit def generalize[A, B, C <: A, D >: B](r: A ~~> B): (C ~~> D) = new (C ~~> D) {
    def perform(a: C) = r.perform(a): D

    def unperform(a: Option[C], out: D): Iterable[C] = 
      try { r.unperform(a.asInstanceOf[A], out).asInstanceOf[Iterable[C]] } catch { case _: Exception => Nil }
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