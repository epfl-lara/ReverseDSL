package perfect
import inox._
import inox.evaluators.EvaluationResults
import inox.trees.{not => inoxNot, _}
import inox.trees.dsl._

import scala.collection.generic.CanBuildFrom

/**
  * Created by Mikael on 31/03/2017.
  */

object StringConcatExtended {
  implicit class AugmentedSubExpr[T <: Expr](e: T) {
    @inline def +&(other: Expr) = StringConcat(e, other)

    /** Simplifies the expression by removing empty string literals*/
    @inline def +<>&(other: Expr) = e match {
      case StringLiteral("") => other
      case _ => other match {
        case StringLiteral("") => e
        case _ => e +& other
      }
    }
  }
  implicit class AugmentedString(e: String) extends AugmentedSubExpr(StringLiteral(e))
  object +& {
    def unapply(e: Expr): Option[(Expr, Expr)] = e match { case StringConcat(a, b) => Some((a, b)) case _ => None }
  }

  implicit class AugmentedBoolean(e: Boolean) {
    @inline def flatMap[A, T[A]](f: => T[A])(implicit canBuildFrom: CanBuildFrom[T[A], A, T[A]]) = {
      if(e) f else {
        val bf = canBuildFrom.apply()
        bf.result()
      }
    }
  }
}