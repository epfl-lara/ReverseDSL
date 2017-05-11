package perfect.core.predef

import perfect.core._

/**
  * Created by Mikael on 09/05/2017.
  */
trait TreeWrapLenses { self: ProgramUpdater with ContExps with Lenses with ADTLenses =>
  def extractTreeWrapGoal(e: Exp): Option[(Exp, Exp => Exp)]

  object TreeWrapLensGoal {
    def unapply(e: Exp) = extractTreeWrapGoal(e)
  }

  object TreeWrapLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case TreeWrapLensGoal(original, wrapper) if in.canDoWrapping =>
          Stream(ContExp(wrapper(in.exp), out.context))
        case _ => Stream.empty
      }
    }
    isPreemptive = true
  }
}



