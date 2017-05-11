package perfect.core.predef

import perfect.core.{ContExps, Lenses, ProgramUpdater}

/**
  * Created by Mikael on 11/05/2017.
  */
trait LetLenses { self: ProgramUpdater with ContExps with Lenses with ApplicationLenses with LambdaLenses =>
  def extractLet(e: Exp): Option[(Var, Exp, Exp)]
  def buildLet(v: Var, assigned: Exp, body: Exp): Exp
  object Let {
    def unapply(e: Exp): Option[(Var, Exp, Exp)] = extractLet(e)
    def apply(v: Var, assigned: Exp, body: Exp): Exp = buildLet(v, assigned, body)
  }

  object LetLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = in.exp match {
      case Let(vd, expr, body) =>
        repair(ContExp(Application(Lambda(Seq(vd), body), Seq(expr)), in.context).wrappingDisabled, out).flatMap {
          case ContExp(Application(Lambda(Seq(vd), body, _), Seq(expr)), f) =>
            List(ContExp(Let(vd, expr, body), f))
          case e  => Nil //throw new Exception(s"Don't know how to get a Let back from $e")
        }
    }
  }
}
