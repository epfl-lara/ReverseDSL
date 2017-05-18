package perfect.lenses

import perfect.InoxProgramUpdater
import perfect.core._
import predef._

/**
  * Created by Mikael on 18/05/2017.
  */
trait ListLibraryExtendedLenses {
  self: InoxProgramUpdater.type =>

  import inox.trees._
  import inox.trees.dsl._
  import perfect.ImplicitTuples._

  object SortWithLens extends SortWithLensLike(InvocationExtractor)

  class SortWithLensLike(Invocation: InvocationExtractor) extends InvocationLensLike(Invocation) {
    def put(originalArgsValues: Seq[ContExp], out: ContExp, builder: Seq[Exp] => Exp)(implicit symbols: Symbols, cache: Cache): Stream[(Seq[ContExp], Cont)] = {
      val ContExp(inExp, inListF) = originalArgsValues.head
      val (inList, inListBuilder) = ListLiteral.unapply(inExp).getOrElse(return Stream.empty)
      val lambdaProg@ContExp(lambdaComp, lambdaF) = originalArgsValues.tail.head

      println("#1")
      // Bidirectionalization for free, we recover the position of the original elements.
      out.simplifiedExpr match {
        case tm@TreeModificationLensGoal(_, at) =>
          val (listGoal, n) = TreeModificationLensGoal.indexOfElemModifiedInList(tm).getOrElse(return Stream.empty)
          /*val subgoal = listGoal match {
            case TreeModificationLensGoal(elemGoal, 0) => elemGoal
            case _ => return Stream.empty
          }*/
          val inVar = extractLambdaUnknownVar(lambdaComp).getOrElse(return Stream.empty)
          val tpe = inVar.getType
          val tpeTupled = inox.trees.ADTType(tuple2, Seq(tpe, Int32Type))

          lazy val tracingLambdaComp = \("in1":: tpeTupled, "in2":: tpeTupled)((in1, in2) =>
            Application(lambdaComp, Seq(in1.getField(_1), in2.getField(_1)))
          )
          lazy val tracingIn = perfect.ListLiteral(inList.zipWithIndex.map{ case (e, i) => _Tuple2(tpe, Int32Type)(e, IntLiteral(i)) }, _TTuple2(tpe, Int32Type))

          val expectedTracingOutput = lambdaF.assignments.flatMap(assign =>
            maybeEvalWithCache(assign(E(perfect.Utils.sortWith)(_TTuple2(tpe, Int32Type))(tracingIn, tracingLambdaComp)))).getOrElse(return Stream.empty)
          lazy val ListLiteral(expectedTracedList, _) = expectedTracingOutput
          lazy val indexOrder = expectedTracedList.map {
            case inox.trees.ADT(_, Seq(_, IntLiteral(i))) => i
          }
          lazy val inverseMap = indexOrder.indices.toList.zip(indexOrder).toMap
          val prev_n = inverseMap(n)


          val inModification= (listGoal /: (prev_n to 1 by -1)) {
            case (r, k) =>
              TreeModificationLensGoal(inListBuilder(inList.take(k)), r, 1)
          }
          Stream((Seq(ContExp(inModification),
            lambdaProg.assignmentsAsOriginals()), Cont()))
        case ListInsertLensGoal(left, inserted, right, listbuilder, listInsertGoalBuilder) => // We care only about deleted elements.
          if(left.length + right.length == inList.length) { // Only inserted elements. We insert them at the end of the original list.
            Stream((Seq(ContExp(listInsertGoalBuilder(inList, inserted, Nil), inListF.assignmentsAsOriginals),
              lambdaProg.assignmentsAsOriginals()), Cont()))
          } else ??? // TODO: Deletions

        case v =>
          throw new Exception("Unexpected case " + v)
      }
    }
  }
}
