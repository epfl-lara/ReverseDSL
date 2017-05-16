package perfect.core
package predef

/**
  * Created by Mikael on 15/05/2017.
  */
trait LetLensesLike { self: ProgramUpdater with ContExps with Lenses with ApplicationLensesLike with LambdaLensesLike =>
  trait LetExtractor {
    def unapply(e: Exp): Option[(Var, Exp, Exp)]
    def apply(v: Var, assigned: Exp, body: Exp): Exp
  }

  class LetLensLike(Application: ApplicationExtractor, Lambda: LambdaExtractor, Let: LetExtractor) extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = in.exp match {
      case Let(vd, expr, body) =>
        repair(ContExp(Application(Lambda(Seq(vd), body), Seq(expr)), in.context).wrappingDisabled, out).flatMap {
          case ContExp(Application(Lambda(Seq(vd), body), Seq(expr)), f) =>
            List(ContExp(Let(vd, expr, body), f))
          case e  => Nil //throw new Exception(s"Don't know how to get a Let back from $e")
        }
      case _ => Stream.empty
    }
  }
}
