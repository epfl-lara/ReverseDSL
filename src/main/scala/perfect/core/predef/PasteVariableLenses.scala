package perfect.core.predef

import perfect.core._


/**
  * Created by Mikael on 09/05/2017.
  */
/** Paste a string variable into a text */
trait PasteVariableLenses { self: ProgramUpdater with ContExps with Lenses with StringLenses with StringConcatLenses =>
  def extractPasteStringVarGoal(e: Exp): Option[(String, Var, String, String, AssociativeInsert.InsertDirection)]

  def buildPasteStringVarGoal(left: String, v: Var, v_value: String, right: String, direction: AssociativeInsert.InsertDirection): Exp

  object PasteVariableLensGoal {
    def unapply(e: Exp) = extractPasteStringVarGoal(e)
    def apply(left: String, v: Var, v_value: String, right: String, direction: AssociativeInsert.InsertDirection) =
      buildPasteStringVarGoal(left, v, v_value, right, direction)
  }


  object PasteVariableLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case PasteVariableLensGoal(left, v2, v2_value, right, direction) =>
          in.exp match {
            case l if isValue(l) =>
              val newExpr = StringLiteral(left) +<>& v2 +<>& StringLiteral(right)
              Stream(ContExp(newExpr, out.context))
            case Var(v) =>
              in.getFunctionValue match {
                case Some(StringLiteral(s)) =>
                  def insertLeft = if(left == s) {
                    if(right != "") {
                      Stream(ContExp(v +& v2 +& StringLiteral(right)))
                    } else {
                      Stream(ContExp(v +& v2))
                    }
                  } else Stream.empty // /:: Log.insertLeft
                  def insertRight = if(right == s) {
                    if(left != "") {
                      Stream(ContExp(StringLiteral(left) +& v2 +& v))
                    } else {
                      Stream(ContExp(v +& v2))
                    }
                  } else Stream.empty // /:: Log.insertRight

                  def propagate = if(left != s && right != s &&
                    s.startsWith(left) && s.endsWith(right) &&
                    s.length >= left.length + right.length ) {
                    // We need to propagate this paste to higher levels.
                    Stream(ContExp(v, out.context combineWith (v -> StrongValue(out.exp))))
                  } else Stream.empty // /:: Log.propagate
                  insertLeft #::: insertRight #::: propagate

                case _ => Stream.empty
              }
            case StringConcat(inLeft, inRight) =>
              val leftValue = in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(inLeft))).getOrElse(return Stream.empty)
              val rightValue = in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(inRight))).getOrElse(return Stream.empty)
              val lv = StringLiteral.unapply(leftValue).getOrElse(return Stream.empty)
              val rv = StringLiteral.unapply(rightValue).getOrElse(return Stream.empty)

              def pasteToLeft: List[((Seq[ContExp], Cont), Int)] = {
                /*Log(s"Right:'$right'")
                Log(s"Right:'$right'")*/
                if(right.endsWith(rv)) { // We did not touch the right part.
                  val newLeft = left
                  val newRight = right.substring(0, right.length - rv.length)
                  val leftPaste = out.subExpr(PasteVariableLensGoal(newLeft, v2, v2_value, newRight, direction))
                  val rightPaste = ContExp(rightValue)
                  val weight = direction match {
                    case AssociativeInsert.InsertToLeft => 0
                    case AssociativeInsert.InsertToRight => 1
                    case AssociativeInsert.InsertAutomatic => typeJump(newLeft, v2_value) + typeJump(v2_value, newRight)
                  }
                  List(((Seq(leftPaste, rightPaste), Cont()), weight)) // /: Log.prefix("pasteToLeft: ")
                } else Nil
              }
              def pasteToRight: List[((Seq[ContExp], Cont), Int)]  = {
                if(left.startsWith(lv)) {
                  val newLeft = left.substring(lv.length)
                  val newRight = right
                  val leftPaste = ContExp(leftValue)
                  val rightPaste = out.subExpr(PasteVariableLensGoal(newLeft, v2, v2_value, newRight, direction))
                  val weight = direction match {
                    case AssociativeInsert.InsertToLeft => 1
                    case AssociativeInsert.InsertToRight => 0
                    case AssociativeInsert.InsertAutomatic => typeJump(newLeft, v2_value) + typeJump(v2_value, newRight)
                  }
                  List(((Seq(leftPaste, rightPaste), Cont()), weight)) // /: Log.prefix("pasteToRight: ")
                } else Nil
              }
              (pasteToLeft ++ pasteToRight).sortBy(_._2).map(_._1).toStream.flatMap{
                case (newArgumentsValues, context) =>
                  for{ argumentsRepairedContext <- ContExp.repairArguments(in.context, Seq(inLeft, inRight).zip(newArgumentsValues))
                       (argumentsRepaired, context2) = argumentsRepairedContext
                  } yield {
                    ContExp(StringConcat(argumentsRepaired(0), argumentsRepaired(1)), context2) combineWith context
                  }
              }
            case _ => Stream.empty
          }
        case _ => Stream.empty
      }
    }
    isPreemptive = true
  }
}



