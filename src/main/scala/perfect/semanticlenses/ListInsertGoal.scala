package perfect.semanticlenses

import inox._
import inox.trees._
import inox.trees.dsl._

/**
  * Created by Mikael on 10/05/2017.
  */
object ListInsertGoal extends FunDefGoal {
  private val InsertList = FreshIdentifier("insertList")

  def apply(tpe: Type, leftUnmodified: List[Expr], inserted: List[Expr], rightUnmodified: List[Expr]): Expr = {
    E(InsertList)(tpe)(
      perfect.ListLiteral(leftUnmodified, tpe),
      perfect.ListLiteral(inserted, tpe),
      perfect.ListLiteral(rightUnmodified, tpe),
      StringLiteral(".") // Not used direction
    )
  }

  def apply(leftUnmodified: List[Expr], inserted: List[Expr], rightUnmodified: List[Expr])(implicit symbols: Symbols): Expr = {
    val tpe = (leftUnmodified ++ inserted ++ rightUnmodified).headOption.map(_.getType).getOrElse(throw new Exception("unable to find type"))
    apply(tpe, leftUnmodified, inserted, rightUnmodified)
  }

  def unapply(e: Expr): Option[(Type, List[Expr], List[Expr], List[Expr])] = {
    e match {
      case FunctionInvocation(InsertList, Seq(tpe0), Seq(
      perfect.ListLiteral(leftBefore, _),
      perfect.ListLiteral(inserted, tpe3),
      perfect.ListLiteral(rightBefore, _),
      _)) =>
        Some((tpe0, leftBefore, inserted, rightBefore))
      case _ => None
    }
  }
  import perfect.Utils

  def funDef = mkFunDef(InsertList)("A"){ case Seq(tA) =>
    (Seq("left"::T(Utils.list)(tA), "inserted"::T(Utils.list)(tA), "right"::T(Utils.list)(tA), "direction"::StringType),
      T(Utils.list)(tA), {
      case Seq(left, inserted, right, direction) =>
        E(Utils.listconcat)(tA)(E(Utils.listconcat)(tA)(
          left,
          inserted),
          right)
    })
  }
}
