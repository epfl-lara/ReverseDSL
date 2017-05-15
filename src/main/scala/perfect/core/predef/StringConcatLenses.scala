package perfect.core.predef

import perfect.core._

/**
  * Created by Mikael on 09/05/2017.
  */

trait StringConcatLenses extends StringConcatLensesLike {
  self: ProgramUpdater with ContExps with Lenses with StringLenses =>
  def extractStringConcat(e: Exp): Option[(Exp, Exp)]
  def buildStringConcat(left: Exp, right: Exp): Exp
  def buildStringConcatSimplified(left: Exp, right: Exp): Exp
  def mkStringVar(name: String, avoid: Var*): Var

  object StringConcat extends StringConcatExtractor {
    def unapply(e: Exp): Option[(Exp, Exp)] = extractStringConcat(e)
    def apply(left: Exp, right: Exp): Exp = buildStringConcat(left, right)
    def apply(): Exp = StringLiteral("")
    def simplified(left: Exp, right: Exp): Exp = buildStringConcatSimplified(left, right)
  }

  object MkStringVar extends MkStringVar {
    def apply(name: String, avoid: Var*): Var = mkStringVar(name, avoid: _*)
  }

  object StringConcatLens extends StringConcatLensLike(StringLiteral, StringConcat, MkStringVar)
}

trait StringConcatLensesLike { self: ProgramUpdater with ContExps with Lenses with StringLensesLike =>
  trait StringConcatExtractor { Self =>
    def unapply(e: Exp): Option[(Exp, Exp)]
    def apply(left: Exp, right: Exp): Exp
    def apply(): Exp
    def simplified(left: Exp, right: Exp): Exp

    object Exhaustive {
      def unapply(e: Exp): Some[List[Exp]] = e match {
        case Self(Exhaustive(a), Exhaustive(b)) => Some(a ++ b)
        case anything => Some(List(anything))
      }
    }

    object Multiple {
      def unapply(e: Exp): Option[List[Exp]] = e match {
        case Exhaustive(l) if l.length >= 2 => Some(l)
        case _ => None
      }

      def apply(s: Seq[Exp]): Exp = s match {
        case Nil => Self()
        case head +: Nil => head
        case head +: tail => Self(head, Self.Multiple(tail))
      }
    }
  }

  trait MkStringVar {
    def apply(name: String, avoid: Var*): Var
  }

  abstract class StringConcatHelpers(StringConcat: StringConcatExtractor) {
    implicit class AugmentedSubExpr[T <: Exp](e: T) {
      @inline def +&(other: Exp): Exp = StringConcat(e, other)

      /** Simplifies the expression by removing empty string literals*/
      @inline def +<>&(other: Exp): Exp = StringConcat.simplified(e, other)
    }
    val +& = StringConcat
  }

  class StringConcatLensLike(StringLiteral: StringLiteralExtractor, StringConcat: StringConcatExtractor, mkStringVar: MkStringVar) extends StringConcatHelpers(StringConcat) with MultiArgsSemanticLens {
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
            (es: Seq[Exp]) => StringConcat(es.head, es(1))
          ))
        case _ => None
      }
    }

    import Utils._

    def typeJump(a: String, b: String): Int = self.typeJump(a, b)

    def put(originalArgsValues: Seq[ContExp], out: ContExp)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ContExp], Cont)] = {
      val newOutput = out.exp
      val leftProgram@ContExp(leftValue, leftF) = originalArgsValues.head
      val rightProgram@ContExp(rightValue, rightF) = originalArgsValues.tail.head
      val lv = StringLiteral.unapply(leftValue).getOrElse(return Stream.empty)
      val rv = StringLiteral.unapply(rightValue).getOrElse(return Stream.empty)

      def leftCase(s: String):  Stream[((Seq[ContExp], Cont), Int)] = {
        //Log.prefix("Testing left:") :=
          if (s.startsWith(lv)) {
            val newRight = s.drop(lv.length)
            val weight = -typeJump(lv, newRight)
            Stream(
              ((Seq(ContExp(leftValue), ContExp(StringLiteral(newRight))), Cont()),
                weight)
            )
          } else Stream.empty // /:: Log.prefix("left worked:")
      }

      def rightCase(s: String): Stream[((Seq[ContExp], Cont), Int)] = {
        //Log.prefix("Testing right:") :=
          if (s.endsWith(rv)) {
            val newLeft = s.take(s.length - rv.length)
            val StringLiteral(left_v) = leftValue
            //Log(s"Computing typeJump(${s.take(s.length - rv.length)}, ${rv})")
            val weight = -typeJump(s.take(s.length - rv.length), rv)
            Stream(((Seq(ContExp(StringLiteral(newLeft)), ContExp(rightValue)), Cont()),
              weight))
          } else Stream.empty // /:: Log.prefix("right worked:")
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
        case StringLiteral(s) =>
          ifEmpty((rightCase(s) .toList++ leftCase(s).toList).sortBy(_._2).map(_._1).toStream) { defaultCase }
        case StringConcat(StringLiteral(left), right) => // Special cases, I don't know if we need them.
          if(lv.startsWith(left)) {
            val newLeftValue = lv.substring(left.length)
            put(Seq(ContExp(StringLiteral(newLeftValue)), rightProgram), out.subExpr(right))
          } else {
            Stream.empty
          }
        case StringConcat(left, StringLiteral(right)) => // Special cases, I don't know if we need them.
          //leftValue = "Hello big " && rightValue == "beautiful world" && right = " world"
          if(rv.endsWith(right)) {
            val newRightValue = rv.substring(0, rv.length - right.length)
            put(Seq(leftProgram, ContExp(StringLiteral(newRightValue))), out.subExpr(left))
          } else {
            Stream.empty
          }
        case Var(v) if out.context.constraints == ExpTrue =>
          out.context.findStrongConstraintValue(v) match {
            case Some(e) =>
              put(Seq(leftProgram, rightProgram), ContExp(e, out.context))
            case _ => defaultCase
          }

        case _ =>
          defaultCase
      }
    }
  }
}
