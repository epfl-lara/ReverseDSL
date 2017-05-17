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
    def named(name: String) = LogLens(this, name)
  }

  ////// Lens combinators

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

  /** Prints a message when executing and after executing the lense. */
  case class LogLens(self: SemanticLens, msg: String) extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      if(debug) println("Entering "+msg)
      val res = self.put(in, out)
      if(debug) println("Exiting "+msg + (if(res.nonEmpty) s" repairing \n$in\nwith\n$out\nGot one solution:\n" + res.head else ""))
      res
    }
    isPreemptive = self.isPreemptive
  }


  /**
    * Created by Mikael on 09/05/2017.
    * Wrapper around a set of indexable lenses by the input program to quickly reach them.
    */
  case class ShortcutLens[A](map: Map[A, SemanticLens], f: Exp => Option[A]) extends SemanticLens {
    override def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      f(in.exp) match {
        case Some(a) => map.get(a) match {
          case Some(lens) => lens.put(in, out)
          case _ =>
            Stream.empty
        }
        case _ => Stream.empty
      }
    }
  }

  /**
    * Created by Mikael on 09/05/2017.
    * Wrapper around a set of indexable output expressions to quickly reach them.
    */
  case class ShortcutGoal[A](map: Map[A, SemanticLens], f: Exp => Option[A]) extends SemanticLens {
    override def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      f(out.simplifiedExpr) match {
        case Some(a) => map.get(a) match {
          case Some(lens) => lens.put(in, out)
          case _ => Stream.empty
        }
        case _ => Stream.empty
      }
    }
  }

  /**
    * Created by Mikael on 08/05/2017.
    * Controls a normal lens. vs a wrapping lens by order of priority.
    * This avoids wrapping around let-expressions (which would be useless)
    */
  case class WrapperLens(normal: SemanticLens, wrapping: SemanticLens) extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      if (in.isWrappingLowPriority) {
        (normal interleave wrapping).put(in, out)
      } else {
        (wrapping interleave normal).put(in, out)
      }
    }
  }

  // Executes lenses in parallel, join on the first element of the results
  // case class ParallelLenses

  /** Saves the stack trace by combining lenses on a balanced tree. */
  def combine(lenses: SemanticLens*): SemanticLens = {
    if(lenses.isEmpty) {
      ValueLens // should not happen
    } else if(lenses.length == 1) lenses(0) else {
      val (left, right) = lenses.splitAt(lenses.length / 2)
      CombinedLens(combine(left: _*), combine(right: _*))
    }
  }

  ////// Lens defaults

  /** Returns the in with assignments unchanged if the out expression is the same. */
  case object NoChangeLens extends SemanticLens {
    isPreemptive = true
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      if(in.exp == out.exp) Stream(in.assignmentsAsOriginals()) else Stream.empty
    }
  }

  /** Replaces the input by the output if the input is a value (with no free variables for lambdas) */
  case object ConstantReplaceLens extends SemanticLens {
    isPreemptive = true
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      // Literals without any free variables should be immediately replaced by the new value
      if(isValue(in.exp) && isValue(out.simplifiedExpr)) Stream(out) else Stream.empty
    }
  }

  /** Replaces the original if the value did not change */
  object ValueLens extends SemanticLens {
    override def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      if(!isVar(out.exp) && in.getFunctionValue.contains(out.exp)) {
        Stream(in.assignmentsAsOriginals() combineWith out.context)
      } else {
        Stream.empty
      }
    }
    isPreemptive = true
  }

  /** If nothing else worked, return nothing with a message. */
  case object FinalLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      println(s"Finished to repair\n$in\n with \n$out")
      Stream.empty
    }
  }

  //////// Lens helpers

  /** Extractor of multiple arguments function calls to reverse.*/
  trait MultipleArgExtractor {
    /** The first argument is the raw list of arguments
      * The second return element is a function which, given an evaluator from the expr to their values with in.context, and out, returns a stream of arguments with a new fomrula.
      * The third return element is a function which recombines multiple arguments into a single expression. */
    def extract(e: Exp)(implicit symbols: Symbols, cache: Cache): Option[
      ( Seq[Exp],
        (Seq[ContExp], ContExp) => Stream[(Seq[ContExp], Cont)],
        Seq[Exp] => Exp
        )]
  }

  trait MultiArgsSemanticLens extends SemanticLens with MultipleArgExtractor {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      extract(in.exp) match {
        case Some((args, wrapper, build)) =>
          (in.context.partialAssignments.map(_._1) match {
            case Some(assign) =>
              val argsOptValue = args.map(arg => maybeEvalWithCache(assign(arg)))
              if (argsOptValue.forall(_.nonEmpty)) {
                val argsContexts = argsOptValue.map(x => in.subExpr(x.get))
                val lenseResult = wrapper(argsContexts, out)
                for {l <- lenseResult; (newArgsValues, newForm) = l
                     a <- ContExp.repairArguments(in.context, args.zip(newArgsValues))
                     (newArguments, newArgumentsContext) = a
                } yield {
                  val context = newForm combineWith newArgumentsContext
                  ContExp(build(newArguments), context)
                }
              } else Stream.empty
            case _ => Stream.empty
          }) #::: {
            extract(out.exp) match { // Unification of arguments if they have the same shape.
              case Some((argsOut, _, _)) =>
                ContExp.repairArguments(in.context, args.zip(argsOut.map(out.subExpr))).map { case (newArguments, context) =>
                  ContExp(build(newArguments), context)
                }
              case _ => Stream.empty[ContExp]
            }
          }

        case _ => Stream.empty
      }
    }
    isPreemptive = false
  }
}
