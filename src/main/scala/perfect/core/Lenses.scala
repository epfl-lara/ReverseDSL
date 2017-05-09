package perfect.core

/**
  * Created by Mikael on 08/05/2017.
  */
trait Lenses { self: ProgramUpdater with ContExps =>
  trait SemanticLens { self =>
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp]
    /** If set to true, when it returns a solution, it discards others */
    var isPreemptive: Boolean = false
    def andThen(other: SemanticLens) = CombinedLens(self, other)
    def interleave(other: SemanticLens) = InterleavedLens(self, other)
  }

  /** Combines two lenses, stopping after the first if it is preemptive */
  case class CombinedLens(self: SemanticLens, other: SemanticLens) extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      if(self.isPreemptive) {
        Utils.ifEmpty(self.put(in, out))(other.put(in, out))
      } else {
        self.put(in, out) #::: other.put(in, out)
      }
    }
    isPreemptive = self.isPreemptive || other.isPreemptive
  }

  /** Interleaves the results of two lenses, starting with the first. */
  case class InterleavedLens(self: SemanticLens, other: SemanticLens) extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      Utils.interleave { self.put(in, out) } {other.put(in, out) }
    }
  }

  /** Returns the in with assignments unchanged if the out expression is the same. */
  case object NoChangeLens extends SemanticLens {
    isPreemptive = true
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      if(in.exp == out.exp) return {
        Stream(in.assignmentsAsOriginals()) // /:: Log.prefix("@return original without constraints:")
      } else Stream.empty
    }
  }

  object ValueLens extends SemanticLens {
    override def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      if(!isVar(out.exp) && in.getFunctionValue == Some(out.exp)) return {
        Stream(in.assignmentsAsOriginals() combineWith out.context) //Log("@return original function");
      } else {
        Stream.empty
      }
    }
    isPreemptive = true
  }



}
