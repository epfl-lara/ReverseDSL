package perfect.core.predef

import perfect.core._

/**
  * Created by Mikael on 09/05/2017.
  */
trait StringInsertLenses { self: ProgramUpdater with ContExps with Lenses with StringLenses with StringConcatLenses with AssociativeLenses =>
  def extractStringInsertGoal(e: Exp): Option[(String, String, String, AssociativeInsert.InsertDirection)]

  def buildStringInsertGoal(left: String, inserted: String, right: String, direction: AssociativeInsert.InsertDirection):
    Exp

  object StringInsertLensGoal {
    def unapply(e: Exp) = extractStringInsertGoal(e)
    def apply(left: String, inserted: String, right: String, direction: AssociativeInsert.InsertDirection) =
      buildStringInsertGoal(left, inserted, right, direction)
  }

  object StringInsertLens extends SemanticLens with AssociativeConcat[String, Char] {
    def endsWith(a: String, b: String): Boolean = a.endsWith(b)
    def startsWith(a: String, b: String): Boolean = a.startsWith(b)
    def length(a: String): Int = a.length
    def take(a: String, i: Int): String = a.substring(0, i)
    def drop(a: String, i: Int): String = a.substring(i)
    def empty: String = ""
    def typeJump(a: String, b: String) = StringInsertLenses.this.typeJump(a, b)

    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case StringInsertLensGoal(leftAfter, inserted, rightAfter, direction) =>
          in.exp match {
            case StringLiteral(_) =>
              Stream(ContExp(StringLiteral(leftAfter + inserted + rightAfter)))
            case StringConcat(expr1, expr2) =>
              val expr1val = in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(expr1))).getOrElse(return Stream.empty)
              val expr2val = in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(expr2))).getOrElse(return Stream.empty)
              val leftValue_s = StringLiteral.unapply(expr1val).getOrElse(return Stream.empty)
              val rightValue_s = StringLiteral.unapply(expr2val).getOrElse(return Stream.empty)
              Utils.ifEmpty {
                associativeInsert(leftValue_s, rightValue_s, leftAfter, inserted, rightAfter,
                  direction,
                  StringLiteral.apply,
                  (l: String, i: String, r: String) => out.subExpr(StringInsertLensGoal(l, i, r, direction))
                ).flatMap { case (args, f) =>
                  ContExp.repairArguments(in.context, Seq((expr1, args(0)), (expr2, args(1)))).map{ case (args2, f2) =>
                    ContExp(StringConcat(args2(0), args2(1)), f combineWith f2 combineWith args(0).context combineWith args(1).context)
                  }
                }
              } {
                // We want to avoid at maximum having to solve constraints.
                Stream(ContExp(in.exp, Cont(Map(), out.exp === in.exp)))
              } #::: {
                out.exp match {
                  // Handles insertion between two non-constants as a possible constant at the last resort.
                  case StringInsertLensGoal(left, inserted, right, direction) if StringLiteral.unapply(expr1).isEmpty && StringLiteral.unapply(expr2).isEmpty &&
                    leftValue_s == left && rightValue_s == right =>
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

