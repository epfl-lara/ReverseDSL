package perfect.semanticlenses

import inox._
import inox.trees._
import inox.trees.dsl._

/**
  * Created by Mikael on 10/05/2017.
  */
object TreeModificationGoal extends FunDefGoal {
  private val Modif = FreshIdentifier("modif")

  def indexOfIdentifier(original: Expr, id: Identifier)(implicit symbols: Symbols): Int = {
    original match {
      case ADT(ADTType(adtid, tpes), _) =>
        symbols.adts(adtid) match {
          case f: ADTConstructor =>
            f.selectorID2Index(id)
          case _ => ???
        }
      case _ => ???
    }
  }

  /** Given an original ADT, a modified children and an index,
    * constructs the goal of replacing the children at the given index by the modified expression */
  def apply(original: Expr, modified: Expr, index: Int)(implicit symbols: Symbols): Expr = {
    original match {
      case ADT(tpe@ADTType(adtid, tpes), args) =>
        symbols.adts(adtid) match {
          case f: ADTConstructor =>
            val f_typed = f.typed(tpes)
            val t = f_typed.fieldsTypes(index)
            E(Modif)(tpe, t)(
              \("x" :: t)(x => ADT(tpe, args.take(index) ++ List(x) ++ args.drop(index + 1))), modified, IntLiteral(index))
          case _ =>
            ???
        }
    }
  }

  def apply(original: Expr, modified: Expr, argsInSequence: List[Identifier])(implicit symbols: Symbols): Expr = {
    argsInSequence match {
      case Nil => modified
      case head::tail =>
        val i = indexOfIdentifier(original, head)
        original match {
          case ADT(tpe, args) =>
            val subgoal = apply(args(i), modified, tail)
            apply(original, subgoal, i)
        }
    }
  }

  /** Recovers the sub-goal with the index leading to it.*/
  def unapply(e: Expr)(implicit symbols: Symbols): Option[(Lambda, Expr, Int)] = {
    List(e) collectFirst {
      case FunctionInvocation(Modif, _, Seq(lambda: Lambda, modified, IntLiteral(index))) =>
        (lambda, modified, index)
    }
  }

  object All {
    /** Requires original to be an ADT, modified to be a sub-goal and indices a valid path in original */
    def apply(original: Expr, modified: Expr, indices: List[Int])(implicit symbols: Symbols): Expr = {
      indices match {
        case Nil => modified
        case head::tail =>
          original match {
            case ADT(_, args) =>
              TreeModification.Goal(original, All.apply(args(head), modified, tail), head)
            case _ => throw new Exception("Unexpected original: "+original+" for indices " + indices)
          }
      }
    }

    /** Recovers the sub-goal with the list of indices leading to it.*/
    def unapply(e: Expr)(implicit symbols: Symbols): Option[(Lambda, Expr, List[Int])] = {
      e match {
        case TreeModificationGoal(Lambda(Seq(x), body), m, index) =>
          m match {
            case All(Lambda(Seq(x2), body2), modified, indices) =>
              val newBody2 = exprOps.replaceFromSymbols(Map(x.toVariable -> body2), body)
              val newLambda = Lambda(Seq(x2), newBody2)
              Some((newLambda, modified, index::indices))
            case modified =>
              val newBody2 = exprOps.replaceFromSymbols(Map(x.toVariable -> modified), body)
              val newLambda = Lambda(Seq(x), newBody2)
              Some((newLambda, modified, List(index)))
          }
        case _ => None
      }
    }
  }


  def funDef = mkFunDef(Modif)("A", "B"){ case Seq(tA, tB) =>
    (Seq("wrapper"::FunctionType(Seq(tB), tA), "tree"::tB, "index"::Int32Type),
      tA, {
      case Seq(wrapper, tree, index) =>
        Application(wrapper, Seq(tree))
    })
  }
}
