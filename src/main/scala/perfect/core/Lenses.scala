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

  case class InterleavedLens(self: SemanticLens, other: SemanticLens) extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      Utils.interleave { self.put(in, out) } {other.put(in, out) }
    }
  }

  case object NoChangeLens extends SemanticLens {
    isPreemptive = true
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      if(in.exp == out.exp) return {
        Stream(in.assignmentsAsOriginals()) // /:: Log.prefix("@return original without constraints:")
      } else Stream.empty
    }
  }
}
