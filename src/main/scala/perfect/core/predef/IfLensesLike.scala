package perfect.core
package predef

/**
  * Created by Mikael on 11/05/2017.
  */
trait IfLensesLike { self: ProgramUpdater with ContExps with Lenses =>
  trait IfExprExtractor {
    def unapply(e: Exp): Option[(Exp, Exp, Exp)]
    def apply(cond: Exp, thn: Exp, elz: Exp): Exp
  }

  class IfLensLike(IfExpr: IfExprExtractor) extends SemanticLens {
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
        case _ => Stream.empty
      }
    }
  }
}
