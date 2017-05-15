package perfect.core.predef

/**
  * Created by Mikael on 15/05/2017.
  */
trait StringInsertLensesLike { self: ProgramUpdater with ContExps with Lenses with StringLensesLike with StringConcatLensesLike with AssociativeLenses =>

  trait StringInsertLensGoalExtractor {
    def unapply(e: Exp): Option[(String, String, String, InsertDirection)]
    def apply(left: String, inserted: String, right: String, direction: AssociativeInsert.InsertDirection): Exp
  }

  class StringInsertLensLike(StringLiteral: StringLiteralExtractor, StringConcat: StringConcatExtractor, StringInsertLensGoal: StringInsertLensGoalExtractor)
      extends StringConcatHelpers(StringConcat) with SemanticLens with AssociativeConcat[String, Char] {
    def endsWith(a: String, b: String): Boolean = a.endsWith(b)
    def startsWith(a: String, b: String): Boolean = a.startsWith(b)
    def length(a: String): Int = a.length
    def take(a: String, i: Int): String = a.substring(0, i)
    def drop(a: String, i: Int): String = a.substring(i)
    def empty: String = ""
    def typeJump(a: String, b: String): Int = self.typeJump(a, b)

    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case StringInsertLensGoal(leftAfter, inserted, rightAfter, direction) =>
          in.exp match {
            case StringLiteral(_) =>
              Stream(ContExp(StringLiteral(leftAfter + inserted + rightAfter)))
            case expr1 +& expr2 =>
              val expr1val = in.maybeEval(expr1).getOrElse(return Stream.empty)
              val expr2val = in.maybeEval(expr2).getOrElse(return Stream.empty)
              val leftValue_s = StringLiteral.unapply(expr1val).getOrElse(return Stream.empty)
              val rightValue_s = StringLiteral.unapply(expr2val).getOrElse(return Stream.empty)
              Utils.ifEmpty {
                associativeInsert(leftValue_s, rightValue_s, leftAfter, inserted, rightAfter,
                  direction,
                  StringLiteral.apply,
                  (l: String, i: String, r: String) => out.subExpr(StringInsertLensGoal(l, i, r, direction))
                ).flatMap { case (args, f) =>
                  ContExp.repairArguments(in.context, Seq((expr1, args.head), (expr2, args(1)))).map{ case (args2, f2) =>
                    ContExp(StringConcat(args2.head, args2(1)), f combineWith f2 combineWith args.head.context combineWith args(1).context)
                  }
                }
              } {
                // We want to avoid at maximum having to solve constraints.
                Stream(ContExp(in.exp, Cont(Map(), out.exp === in.exp)))
              } #::: {
                if(StringLiteral.unapply(expr1).isEmpty && StringLiteral.unapply(expr2).isEmpty &&
                    leftValue_s == leftAfter && rightValue_s == rightAfter) {
                  Stream(in.subExpr(expr1 +& StringLiteral(inserted) +& expr2).assignmentsAsOriginals())
                } else Stream.empty
              }
            case _ => Stream.empty
          }
      }
    }
  }
}
