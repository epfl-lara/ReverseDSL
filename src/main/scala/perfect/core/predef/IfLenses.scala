package perfect.core.predef

import perfect.core.{ContExps, Lenses, ProgramUpdater}

/**
  * Created by Mikael on 11/05/2017.
  */
trait IfLenses { self: ProgramUpdater with ContExps with Lenses =>
  def extractIf(e: Exp): Option[(Exp, Exp, Exp)]
  def buildIf(cond: Exp, thn: Exp, elz: Exp): Exp

  object IfExpr {
    def unapply(e: Exp) = extractIf(e)
    def apply(cond: Exp, thn: Exp, elz: Exp) = buildIf(cond, thn, elz)
  }

  object IfLens extends SemanticLens {
    override def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      in.exp match {
        case IfExpr(cond, thenn, elze) =>
          val cond_v = in.maybeEval(cond).getOrElse(return Stream.Empty)
          cond_v match {
            case b if b == ExpTrue =>
              for(pf <- repair(in.subExpr(thenn), out)) yield
                pf.wrap(x => IfExpr(cond, x, elze))
            case b if b == ExpFalse =>
              for(pf <- repair(in.subExpr(elze), out)) yield
                pf.wrap(x => IfExpr(cond, thenn, x))
            case _ => Stream.empty // throw new Exception(s"Not a boolean: $cond_v")
          }
      }
    }
  }
}
