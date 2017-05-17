package perfect.core
package predef

/**
  * Created by Mikael on 17/05/2017.
  */
trait ListConcatLensesLike { self: ProgramUpdater with ContExps with Lenses with ListLensesLike  =>
  trait ListConcatExtractor {
    def unapply(e: Exp): Option[(Exp, Exp, (Exp, Exp) => Exp)]
    def apply(left: Exp, right: Exp)(implicit symbols: Symbols): Exp
  }

  /** Lense-like list concat, with the possibility of changing the mapping lambda. */
  class ListConcatLensLike(ListLiteral: ListLiteralExtractor, ListConcat: ListConcatExtractor) extends MultiArgsSemanticLens {
    def extract(e: Exp)(implicit symbols: Symbols, cache: Cache): Option[
      ( Seq[Exp],
        (Seq[ContExp], ContExp) => Stream[(Seq[ContExp], Cont)],
        Seq[Exp] => Exp
        )] = e match {
      case ListConcat(left, right, builder) =>
        Some((Seq(left, right),
          (originalArgsValues: Seq[ContExp], out: ContExp) => put(originalArgsValues, out),
          (x: Seq[Exp]) => builder(x.head, x(1)))
        )
      case _ => None
    }

    def put(originalArgsValues: Seq[ContExp], newOutputProgram: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[(Seq[ContExp], Cont)] = {
      val newOutput = newOutputProgram.exp
      val ContExp(leftValue, leftF) = originalArgsValues.head
      val ContExp(rightValue, rightF) = originalArgsValues.tail.head
      val (leftValue_s, listBuilder) = ListLiteral.unapply(leftValue).getOrElse(return Stream.empty)
      val (rightValue_s, _) = ListLiteral.unapply(rightValue).getOrElse(return Stream.empty)

      def defaultCase: Stream[(Seq[ContExp], Cont)] = {
        val left = varFromExp("l", leftValue)
        val right = varFromExp("r", rightValue)
        //Log(s"List default case: ${left.id} + ${right.id} == $newOutput")

        val f = Cont(Map(
          left -> OriginalValue(leftValue),
          right -> OriginalValue(rightValue)))

        if(isVar(newOutput)) {
          Stream((Seq(
            ContExp(left, left -> OriginalValue(leftValue)),
            ContExp(right, right -> OriginalValue(rightValue))),
            f combineWith Cont(
              Map(newOutput.asInstanceOf[Var] -> StrongValue(ListConcat(left, right)),
                left -> OriginalValue(leftValue),
                right -> OriginalValue(rightValue)))))
        } else
          Stream((Seq(
            ContExp(left, left -> OriginalValue(leftValue)),
            ContExp(right, right -> OriginalValue(rightValue))), f combineWith Cont(Map(), newOutput === ListConcat(left, right))))
      }

      // Prioritize changes that touch only one of the two expressions.
      newOutput match {
        case ListLiteral(s, listBuilder) =>
          (leftValue match {
            case ListLiteral(lv, _) =>
              if (s.startsWith(lv)) {
                Stream((Seq(ContExp(leftValue), ContExp(listBuilder(s.drop(lv.length)))), Cont()))
              } else Stream.empty
            case _ => Stream.empty
          }) #::: (
            rightValue match {
              case ListLiteral(rv, _) =>
                if (s.endsWith(rv)) {
                  Stream((Seq(ContExp(listBuilder(s.take(s.length - rv.length))), ContExp(rightValue)), Cont()))
                } else Stream.empty
              case _ => Stream.empty
            }
            ) #::: defaultCase
        case Var(newOut) => defaultCase
        case _ => Stream.empty
      }
    }
  }
}
