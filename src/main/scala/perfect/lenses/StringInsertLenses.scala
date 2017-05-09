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
trait StringInsertLenses { self: InoxProgramUpdater.type with StringConcatLenses =>
  object StringInsertLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case StringConcat(outArg1, outArg2) =>
          in.exp match {
            case StringConcat(expr1, expr2) =>
              ContExp.repairArguments(in.context, Seq((expr1, out.subExpr(outArg1)), (expr2, out.subExpr(outArg2)))).map{ case (args, f) =>
                ContExp(StringConcat(args(0), args(1)), f)
              }
            case _ => Stream.empty
          }
        case _ =>
          in.exp match {
            case StringLiteral(_) =>
              out.exp match {
                case StringInsertGoal(left, inserted, right, direction) =>
                  Stream(ContExp(StringLiteral(left + inserted + right)))
                case _ => Stream(out)
              }
            case StringConcat(expr1, expr2) =>
              val expr1val = in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(expr1)))
              val expr2val = in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(expr2)))
              Utils.ifEmpty {
                if (expr1val.isEmpty || expr2val.isEmpty) {
                  Stream.empty
                } else {
                  val expr1v = expr1val.get
                  val expr2v = expr2val.get
                  StringConcatLens.put(Seq(in.subExpr(expr1v), in.subExpr(expr2v)), out).flatMap { case (args, f) =>
                    ContExp.repairArguments(in.context, Seq((expr1, args(0)), (expr2, args(1)))).map{ case (args2, f2) =>
                      ContExp(StringConcat(args2(0), args2(1)), f combineWith f2 combineWith args(0).context combineWith args(1).context)
                    }
                  }
                }
              } {
                // We want to avoid at maximum having to solve constraints.
                Stream(ContExp(in.exp, Cont(Map(), out.exp === in.exp)))
              } #::: {
                out.exp match {
                  // Handles insertion between two non-constants as a possible constant at the last resort.
                  case StringInsertGoal(left, inserted, right, direction) if !expr1.isInstanceOf[StringLiteral] && !expr2.isInstanceOf[StringLiteral] &&
                    expr1val == Some(StringLiteral(left)) &&
                    expr2val == Some(StringLiteral(right)) =>
                    Stream(in.subExpr(expr1 +& StringLiteral(inserted) +& expr2).assignmentsAsOriginals())
                  case _ => Stream.empty
                }
              }
            case _ => Stream.empty
          }
      }
    }
  }
}

object StringInsertGoal extends FunDefGoal {
  private val InsertString = FreshIdentifier("insertString")
  import perfect.core.predef.AssociativeInsert
  import AssociativeInsert._

  def apply(left: String, s: String, right: String, direction: InsertDirection): Expr = {
    E(InsertString)(StringLiteral(left), StringLiteral(s), StringLiteral(right), StringLiteral(direction.toString))
  }

  def unapply(e: Expr): Option[(String, String, String, InsertDirection)] = {
    e match {
      case FunctionInvocation(InsertString, Seq(), Seq(
      StringLiteral(leftBefore), StringLiteral(inserted), StringLiteral(rightBefore), StringLiteral(AssociativeInsert(direction))
      )) =>
        Some((leftBefore, inserted, rightBefore, direction))
      case _ =>
        None
    }
  }

  def funDef = mkFunDef(InsertString)(){ case _ =>
    (Seq("left"::StringType, "inserted"::StringType, "right"::StringType, "direction"::StringType),
      StringType,
      {
        case Seq(left, inserted, right, direction) =>
          left +& inserted +& right // Dummy
      })
  }
}