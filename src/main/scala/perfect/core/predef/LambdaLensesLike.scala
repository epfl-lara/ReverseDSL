package perfect.core
package predef

/**
  * Created by Mikael on 15/05/2017.
  */
trait LambdaLensesLike { self: ProgramUpdater with ContExps with Lenses =>
  //Returns the variables used, the inner body, a way to produce fresh variables, and a way to rebuild the original lambda given a new body
  trait LambdaExtractor {
    def unapply(e: Exp): Option[(Seq[Var], Exp, Exp => Exp)]
    def apply(v: Seq[Var], body: Exp): Exp
  }

  class LambdaLensLike(Lambda: LambdaExtractor) extends SemanticLens {
    isPreemptive = true
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      in.exp match {
        case fun@Lambda(vds, body, lambdaBuilder) =>
          val fvfun = freeVariables(fun)
          /** Replaces the vds by universally quantified variables */
          def unify: Stream[ContExp] = {
            if(fvfun.nonEmpty) {
              out.forcedExpr match {
                case Lambda(vds2, body2, builder2) =>
                  val freshVariables1 = vds.map((x: Var) => freshen(x))
                  val map1 = vds.zip(freshVariables1).toMap
                  val map2 = vds2.zip(freshVariables1).toMap
                  val freshBody1 = postMap{
                    case Var(v) => map1.get(v)
                    case _ => None}(body)
                  val freshBody2 = postMap{
                    case Var(v) => map2.get(v)
                    case _ => None}(body2)

                  val universallyQuantified = Cont(freshVariables1.map(v => v -> AllValues).toMap)
                  val mapR = freshVariables1.zip(vds).toMap
                  for{ pf <- repair(in.subExpr(freshBody1) combineWith universallyQuantified,
                                   out.subExpr(freshBody2) combineWith universallyQuantified) } yield {
                    pf.wrap { newBody =>
                      val abstractedBody = postMap{
                        case Var(v) => mapR.get(v)
                        case _ => None
                      }(newBody)
                      lambdaBuilder(abstractedBody)
                    }
                  }
                case _ => Stream.empty
              }
            } else {
              Stream.empty
            }
          }

          def justOut: Stream[ContExp] = {
            if(fvfun.nonEmpty) { // We still need to assign an original value to these variables.
              Stream(out combineWith in.context.assignmentsAsOriginals)
            } else Stream(out)
          }

          unify #::: justOut
        case _ => Stream.empty
      }
    }
  }
}
