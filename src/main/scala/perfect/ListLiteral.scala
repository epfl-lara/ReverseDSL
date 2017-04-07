package perfect

import Utils._
import inox.trees._

/**
  * Created by Mikael on 06/04/2017.
  */
object ListLiteral {
  import Utils._
  def unapply(e: Expr): Option[(List[Expr], Type)] = e match {
    case ADT(ADTType(cons, Seq(tp)), Seq(head, tail)) =>
      unapply(tail).map(res => (head :: res._1, tp))
    case ADT(ADTType(nil, Seq(tp)), Seq()) =>
      Some((Nil, tp))
    case _ => None
  }
  def apply(e: List[Expr], tp: Type): Expr = e match {
    case head :: tail =>
      ADT(ADTType(cons, Seq(tp)), Seq(head, apply(tail, tp)))
    case Nil =>
      ADT(ADTType(nil, Seq(tp)), Seq())
  }
  /** Requires either f to be empty, or e to be a ListLiteral */
  def concat(e: Expr, f: Expr*): Expr = {
    if(f.isEmpty) e else {
      e match {
        case ADT(ADTType(cons, Seq(tp)), Seq(head, tail)) =>
          ADT(ADTType(cons, Seq(tp)), Seq(head, concat(tail, f: _*)))
        case ADT(ADTType(nil, Seq(tp)), Seq()) =>
          concat(f.head, f.tail: _*)
        case _ => throw new Exception("[internal error] cannot concatenate non-literal on the left using ListLiteral.concat")
      }
    }
  }
}
