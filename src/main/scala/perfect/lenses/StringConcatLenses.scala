package perfect.lenses

import perfect.InoxProgramUpdater
import perfect.StringConcatExtended
import inox._
import inox.trees._
import inox.trees.dsl._

/**
  * Created by Mikael on 09/05/2017.
  */
trait StringConcatLenses { self: InoxProgramUpdater.type =>

  def mkStringVar(name: String, avoid: Var*): Var

  case object StringConcatLens extends MultiArgsSemanticLens with AssociativeConcat[String, Char] {
    def extract(e: Exp)(implicit cache: Cache, symbols: Symbols): Option[(
      Seq[Exp],
        (Seq[ContExp], ContExp) => Stream[(Seq[ContExp], Cont)],
        Seq[Exp] => Exp)] = {
      e match {
        case StringConcat(e1, e2) =>
          Some((Seq(e1, e2),
            (originalArgsValues: Seq[ContExp], out: ContExp) => {
              put(originalArgsValues, out)
            },
            (es: Seq[Exp]) => StringConcat(es(0), es(1))
          ))
        case _ => None
      }
    }


    import StringConcatExtended._
    import Utils._
    val identifier = FreshIdentifier("tmpstringconcat")

    def endsWith(a: String, b: String): Boolean = a.endsWith(b)
    def startsWith(a: String, b: String): Boolean = a.startsWith(b)
    def length(a: String): Int = a.length
    def take(a: String, i: Int): String = a.substring(0, i)
    def drop(a: String, i: Int): String = a.substring(i)
    def empty: String = ""

    @inline def charType(a: Char): Int =
      if(a.isUpper) 1 else if(a.isLower) 2 else if(a.isSpaceChar) 5 else if(a == '\n' || a == '\r') 10 else 4 // 4 for punctuation.

    @inline def differentCharType(a: Char, b: Char): Int = {
      Math.abs(charType(a) - charType(b))
    }

    @inline def typeJump(a: String, b: String): Int = {
      (if(a.nonEmpty && b.nonEmpty)
        differentCharType(a(a.length - 1), b(0))
      else 0) // We mostly insert into empty strings if available.
    }

    def put(originalArgsValues: Seq[ContExp], out: ContExp)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ContExp], Cont)] = {
      val newOutput = out.exp
      val leftProgram@ContExp(leftValue@StringLiteral(lv), leftF) = originalArgsValues.head
      val rightProgram@ContExp(rightValue@StringLiteral(rv), rightF) = originalArgsValues.tail.head

      def leftCase(s: String):  Stream[((Seq[ContExp], Cont), Int)] = {
        //Log.prefix("Testing left:") :=
          (if (s.startsWith(lv)) {
            val newRight = s.drop(lv.length)
            val weight = -typeJump(lv, newRight)
            Stream(
              ((Seq(ContExp(leftValue), ContExp(StringLiteral(newRight))), Cont()),
                weight)
            )
          } else Stream.empty) // /:: Log.prefix("left worked:")
      }

      def rightCase(s: String): Stream[((Seq[ContExp], Cont), Int)] = {
        //Log.prefix("Testing right:") :=
          (if (s.endsWith(rv)) {
            val newLeft = s.take(s.length - rv.length)
            val StringLiteral(left_v) = leftValue
            //Log(s"Computing typeJump(${s.take(s.length - rv.length)}, ${rv})")
            val weight = -typeJump(s.take(s.length - rv.length), rv)
            Stream(((Seq(ContExp(StringLiteral(newLeft)), ContExp(rightValue)), Cont()),
              weight))
          } else Stream.empty) // /:: Log.prefix("right worked:")
      }

      def defaultCase: Stream[(Seq[ContExp], Cont)] = {
        val left = mkStringVar("l")
        val right = mkStringVar("r")
        //Log(s"String default case: ${left.id} + ${right.id} == $newOutput:")

        val f = Cont(Map(
          left -> OriginalValue(leftValue),
          right -> OriginalValue(rightValue)))//, not(left === leftValue) || not(right === rightValue))
        if(isVar(newOutput)) {
          Stream((Seq(
            ContExp(left, left -> OriginalValue(leftValue)),
            ContExp(right, right -> OriginalValue(rightValue))),
            f combineWith Cont(
              Map(newOutput.asInstanceOf[Var] -> StrongValue(left +& right),
                left -> OriginalValue(leftValue),
                right -> OriginalValue(rightValue)))))
        } else
          Stream((Seq(
            ContExp(left, left -> OriginalValue(leftValue)),
            ContExp(right, right -> OriginalValue(rightValue))), f combineWith Cont(Map(), newOutput === left +& right)))
      }

      // Prioritize changes that touch only one of the two expressions.
      out.exp match {
        case StringInsertGoal(leftAfter, inserted, rightAfter, direction) =>
          val StringLiteral(rightValue_s) = rightValue
          val StringLiteral(leftValue_s) = leftValue

          associativeInsert(leftValue_s, rightValue_s, leftAfter, inserted, rightAfter,
            direction,
            StringLiteral,
            (l: String, i: String, r: String) => out.subExpr(StringInsertGoal(l, i, r, direction))
          )
        case pc@PatternMatchGoal.CloneTextMultiple(left, List((cloned, variable, right))) => // TODO support for direct clone of multiple variables.
          def cloneToLeft: List[(Seq[ContExp], Cont)] = {
            if(right.endsWith(rv)) {
              val newLeft = left
              val newRight = right.substring(0, right.length - rv.length)
              val leftClone = out.subExpr(PatternMatchGoal.CloneTextMultiple(newLeft, List((cloned, variable, newRight))))
              val rightClone = ContExp(rightValue)
              List((Seq(leftClone, rightClone), Cont())) // /: Log.prefix("cloneToLeft: ")
            } else Nil
          }
          def cloneToRight: List[(Seq[ContExp], Cont)] = {
            if(left.startsWith(lv)) {
              val newLeft = left.substring(lv.length)
              val newRight = right
              val leftPaste = ContExp(leftValue)
              val rightPaste = out.subExpr(PatternMatchGoal.CloneTextMultiple(newLeft, List((cloned, variable, newRight))))
              List((Seq(leftPaste, rightPaste), Cont())) // /: Log.prefix("cloneToRight: ")
            } else Nil
          }
          // If the clone overlaps the two arguments
          def cloneBoth: List[(Seq[ContExp], Cont)] = {
            if(!left.startsWith(lv)&& !right.endsWith(rv) &&
              lv.startsWith(left) && rv.endsWith(right)) {
              val leftCloned = cloned.substring(0, lv.length - left.length)
              val rightCloned = cloned.substring(lv.length - left.length)
              val leftVar = mkStringVar(leftCloned, variable)
              val leftClone = out.subExpr(PatternMatchGoal.CloneTextMultiple(left, List((leftCloned, leftVar, ""))))
              val rightVar = mkStringVar(rightCloned, variable, leftVar)
              val rightClone = out.subExpr(PatternMatchGoal.CloneTextMultiple("", List((rightCloned, rightVar, right))))
              List((Seq(leftClone, rightClone), Cont(variable -> InsertVariable(leftVar +& rightVar))))
            } else Nil
          }
          (cloneToLeft ++ cloneToRight ++ cloneBoth).toStream

        case pv@PasteVariableGoal(left, v, v_value, right, direction) =>
          def pasteToLeft: List[((Seq[ContExp], Cont), Int)] = {
            /*Log(s"Right:'$right'")
            Log(s"Right:'$right'")*/
            if(right.endsWith(rv)) { // We did not touch the right part.
              val newLeft = left
              val newRight = right.substring(0, right.length - rv.length)
              val leftPaste = out.subExpr(PasteVariableGoal(newLeft, v, v_value, newRight, direction))
              val rightPaste = ContExp(rightValue)
              val weight = direction match {
                case PasteVariableGoal.PasteToLeft => 0
                case PasteVariableGoal.PasteToRight => 1
                case PasteVariableGoal.PasteAutomatic => typeJump(newLeft, v_value) + typeJump(v_value, newRight)
              }
              List(((Seq(leftPaste, rightPaste), Cont()), weight)) // /: Log.prefix("pasteToLeft: ")
            } else Nil
          }
          def pasteToRight: List[((Seq[ContExp], Cont), Int)]  = {
            if(left.startsWith(lv)) {
              val newLeft = left.substring(lv.length)
              val newRight = right
              val leftPaste = ContExp(leftValue)
              val rightPaste = out.subExpr(PasteVariableGoal(newLeft, v, v_value, newRight, direction))
              val weight = direction match {
                case PasteVariableGoal.PasteToLeft => 1
                case PasteVariableGoal.PasteToRight => 0
                case PasteVariableGoal.PasteAutomatic => typeJump(newLeft, v_value) + typeJump(v_value, newRight)
              }
              List(((Seq(leftPaste, rightPaste), Cont()), weight)) // /: Log.prefix("pasteToRight: ")
            } else Nil
          }
          (pasteToLeft ++ pasteToRight).sortBy(_._2).map(_._1).toStream
        case StringLiteral(s) =>
          ifEmpty((rightCase(s) .toList++ leftCase(s).toList).sortBy(_._2).map(_._1).toStream) { defaultCase }
        case StringConcat(StringLiteral(left), right) =>
          if(lv.startsWith(left)) {
            val newLeftValue = lv.substring(left.length)
            put(Seq(ContExp(StringLiteral(newLeftValue)), rightProgram), out.subExpr(right))
          } else {
            ???
          }
        case StringConcat(left, StringLiteral(right)) => // TODO !!
          //leftValue = "Hello big " && rightValue == "beautiful world" && right = " world"
          if(rv.endsWith(right)) {
            val newRightValue = rv.substring(0, rv.length - right.length)
            put(Seq(leftProgram, ContExp(StringLiteral(newRightValue))), out.subExpr(left))
          } else {
            ???
          }
        case Var(v) if out.context.constraints == BooleanLiteral(true) =>
          out.context.findStrongConstraintValue(v) match {
            case Some(e) =>
              put(Seq(leftProgram, rightProgram), ContExp(e, out.context))
            case _ => defaultCase
          }

        case _ =>
          defaultCase
      }
    }

    // Concat definition in inox
    val funDef = mkFunDef(identifier)(){ case _ =>
      (Seq("a" :: StringType, "b" :: StringType),
        StringType,
        { case Seq(left, right) =>
          StringConcat(left, right)
        })
    }
  }
}
