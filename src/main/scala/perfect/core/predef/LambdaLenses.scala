package perfect.core.predef

import perfect.core.{ContExps, Lenses, ProgramUpdater}

/**
  * Created by Mikael on 05/05/2017.
  */

trait LambdaLenses extends LambdaLensesLike { self: ProgramUpdater with ContExps with Lenses =>
  def extractLambda(e: Exp): Option[(Seq[Var], Exp, Exp => Exp)]
  def buildLambda(v: Seq[Var], body: Exp): Exp

  object Lambda extends LambdaExtractor {
    def unapply(e: Exp): Option[(Seq[Var], Exp, Exp => Exp)] = extractLambda(e)
    def apply(v: Seq[Var], body: Exp): Exp = buildLambda(v, body)
  }

  object LambdaLens extends LambdaLensLike(Lambda)
}

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
          /** Replaces the vds by universally quantified variables */
          def unify: Stream[ContExp] = {
            if(freeVariables(fun).nonEmpty) {
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

          unify #::: Stream(out)
        case _ => Stream.empty
      }
    }
  }
}
