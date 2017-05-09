package perfect.lenses

import inox.trees
import perfect.InoxProgramUpdater
import inox.{FreshIdentifier, Identifier}
import perfect.InoxProgramUpdater
import perfect.semanticlenses.TreeWrap
import inox.trees._
import inox._
import inox.trees.dsl._
import perfect.StringConcatExtended._


/**
  * Created by Mikael on 09/05/2017.
  */
/** Paste a string variable into a text */
trait PasteVariableLenses { self: InoxProgramUpdater.type =>
  object PasteVariableLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case PasteVariableGoal(left, v2, v2_value, right, direction) =>
          in.exp match {
            case l: Literal[_] =>
              val newExpr = StringLiteral(left) +<>& v2 +<>& StringLiteral(right)
              Stream(ContExp(newExpr, out.context))
            case v@Variable(id, tpe, flags) =>
              in.getFunctionValue match {
                case Some(StringLiteral(s)) =>
                  def insertLeft = (if(left == s) {
                    if(right != "") {
                      Stream(ContExp(v +& v2 +& StringLiteral(right)))
                    } else {
                      Stream(ContExp(v +& v2))
                    }
                  } else Stream.empty) // /:: Log.insertLeft
                  def insertRight = (if(right == s) {
                    if(left != "") {
                      Stream(ContExp(StringLiteral(left) +& v2 + v))
                    } else {
                      Stream(ContExp(v +& v2))
                    }
                  } else Stream.empty) // /:: Log.insertRight

                  def propagate = (if(left != s && right != s &&
                    s.startsWith(left) && s.endsWith(right) &&
                    s.length >= left.length + right.length ) {
                    // We need to propagate this paste to higher levels.
                    Stream(ContExp(v, out.context combineWith (v -> StrongValue(out.exp))))
                  } else Stream.empty) // /:: Log.propagate
                  insertLeft #::: insertRight #::: propagate

                case _ => Stream.empty
              }


            case _ => Stream.empty
          }
        case _ => Stream.empty
      }
    }
    isPreemptive = true
  }
}


object PasteVariableGoal extends Enumeration with FunDefGoal {
  type PasteDirection = Value
  val PasteToLeft, PasteToRight, PasteAutomatic = Value
  private object Direction {
    def unapply(s: String): Option[PasteDirection] =
      values.find(_.toString == s)
  }

  private val Paste = FreshIdentifier("pastevariable")
  def apply(left: String, insertedVar: Variable, originalVarValue: String, right: String, direction: PasteDirection): Expr = {
    E(Paste)(
      StringLiteral(left),
      insertedVar,
      StringLiteral(originalVarValue),
      StringLiteral(right),
      StringLiteral(direction.toString)
    )
  }

  def unapply(f: Expr): Option[(String, Variable, String, String, PasteDirection)] = {
    f match {
      case FunctionInvocation(Paste, Seq(), Seq(
      StringLiteral(leftBefore),
      inserted: Variable,
      StringLiteral(insertedValue),
      StringLiteral(rightBefore),
      StringLiteral(Direction(direction))
      )) =>
        Some((leftBefore, inserted, insertedValue, rightBefore, direction))
      case _ =>
        None
    }
  }

  def funDef = mkFunDef(Paste)(){ case _ =>
    (Seq("left"::StringType, "pasted"::StringType,  "originalvalue"::StringType, "right"::StringType, "direction"::StringType),
      StringType,
      {
        case Seq(left, pasted, originalvalue, right, direction) =>
          left +& originalvalue +& right // Dummy
      })
  }
}
