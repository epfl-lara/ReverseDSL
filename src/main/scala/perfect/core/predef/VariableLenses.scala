package perfect.core.predef

import perfect.core.{ContExps, Lenses, ProgramUpdater}

/**
  * Created by Mikael on 11/05/2017.
  */
trait VariableLenses { self: ProgramUpdater with ContExps with Lenses =>
  object VariableLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      in.exp match {
        // Variables are assigned the given value, and repaired later if needed.
        case Var(v) => Stream(ContExp(v, out.context combineWith Cont(v -> StrongValue(out.exp))))
        case _ => Stream.empty
      }
    }
    isPreemptive = true
  }
}
