package perfect.core.predef

import perfect.core.{ContExps, Lenses, ProgramUpdater}

/**
  * Created by Mikael on 11/05/2017.
  */
trait AsInstanceOfLenses { self: ProgramUpdater with ContExps with Lenses =>
  /** Returns the inner element and a wrapper around it. */
  def extractAsInstanceOf(e: Exp): Option[(Exp, Exp => Exp)]

  object AsInstanceOf {
    def unapply(e: Exp) = extractAsInstanceOf(e)
  }

  object AsInstanceOfLens extends SemanticLens {
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
