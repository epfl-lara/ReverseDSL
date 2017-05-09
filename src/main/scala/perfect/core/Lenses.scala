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

  /** Extractor of multiple arguments function calls to reverse.*/
  trait MultipleArgExtractor {
    /** The first argument is the raw list of arguments
      * The second return element is a function which, given an evaluator from the expr to their values with in.formula, and out, returns a stream of arguments with a new fomrula.
      * The third return element is a function which recombines multiple arguments into a single expression. */
    def extract(e: Exp)(implicit cache: Cache, symbols: Symbols): Option[
      ( Seq[Exp],
        (Seq[ContExp], ContExp) => Stream[(Seq[ContExp], Cont)],
        Seq[Exp] => Exp
        )]
  }

  trait MultiArgsSemanticLens extends SemanticLens with MultipleArgExtractor {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      extract(in.exp) match {
        case Some((args, wrapper, build)) =>
          in.context.partialAssignments.map(_._1) match {
            case Some(assign) =>
              val argsOptValue = args.map(arg => maybeEvalWithCache(assign(arg)))
              if (argsOptValue.forall(_.nonEmpty)) {
                val argsFormulas = argsOptValue.map(x => in.subExpr(x.get))
                val lenseResult = wrapper(argsFormulas, out)
                for {l <- lenseResult; (newArgsValues, newForm) = l
                     a <- ContExp.repairArguments(in.context, args.zip(newArgsValues))
                     (newArguments, newArgumentsFormula) = a
                } yield {
                  val formula = newForm combineWith newArgumentsFormula
                  ContExp(build(newArguments), formula)
                }
              }
              else Stream.empty
            case None => Stream.empty
          }

        case _ => Stream.empty
      }
    }
    isPreemptive = false
  }


  /**
    * Created by Mikael on 09/05/2017.
    * Wrapper around a set of indexable lenses to quickly reach them.
    */
  case class ShortcutLens[A](map: Map[A, SemanticLens], f: Exp => Option[A]) extends SemanticLens {
    override def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      f(in.exp) match {
        case Some(a) => map.get(a) match {
          case Some(lens) => lens.put(in, out)
          case _ => Stream.empty
        }
        case _ => Stream.empty
      }
    }
  }
}
