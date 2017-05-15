package perfect.core
package predef

/**
  * Created by Mikael on 15/05/2017.
  */
trait AsInstanceOfLensesLike { self: ProgramUpdater with ContExps with Lenses =>
  trait AsInstanceOfExtractor {
    def unapply(e: Exp): Option[(Exp, Exp => Exp)]
  }

  class AsInstanceOfLensLike(AsInstanceOf: AsInstanceOfExtractor) extends SemanticLens {
    override def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      in.exp match {
        case AsInstanceOf(a, builder) =>
          for{ p <- repair(in.subExpr(a), out)} yield p.wrap(x => builder(x) )
        case anyExpr =>
          Stream.empty
      }
    }
  }
}
