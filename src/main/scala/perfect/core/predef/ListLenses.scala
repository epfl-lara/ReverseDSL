package perfect.core
package predef


/**
  * Created by Mikael on 09/05/2017.
  *
  * Make sure the symbols contain the reference to the filter function taht it is mapped to.
  */
trait ListLenses { self: ProgramUpdater with ContExps with Lenses with InvocationLenses =>
  /** Returns the elements and a builder to build back the list. */
  def extractList(e: Exp): Option[(List[Exp], List[Exp] => Exp)]

  def Application(lambda: Exp, args: Seq[Exp]): Exp

  object ListLiteral {
    def unapply(e: Exp) = extractList(e)
  }

  /** Lense-like filter */
  case object FilterLens extends SemanticLens with FilterLike[Exp] with MultiArgsSemanticLens { // TODO: Incorporate filterRev as part of the sources.
    def extract(e: Exp)(implicit cache: Cache, symbols: Symbols): Option[( Seq[Exp],
      (Seq[ContExp], ContExp) => Stream[(Seq[ContExp], Cont)],
      Seq[Exp] => Exp
      )] = {
      extractInvocation(e) match {
        case Some((args, builder)) =>
          Some((args,
                (argValues: Seq[ContExp], out: ContExp) => {
                   put(argValues, out, builder)
                },
                builder
          ))

        case None => None
      }
    }

    def put(originalArgsValues: Seq[ContExp], newOutputProgram: ContExp, builder: Seq[Exp] => Exp)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ContExp], Cont)] = {
      val ContExp(lambda, lambdaF) = originalArgsValues.tail.head
      val newOutput = newOutputProgram.exp
      val ContExp(ListLiteral(originalInput, listBuilder), listF) = originalArgsValues.head
      //Log(s"FilterLens: $originalArgsValues => $newOutputProgram")
      val filterLambda = (expr: Exp) => lambdaF.assignments.flatMap(assign => maybeEvalWithCache(assign(Application(lambda, Seq(expr))))) contains ExpTrue
      newOutput match {
        case ListLiteral(newOutputList, _) =>
          filterRev(originalInput, filterLambda, newOutputList).map{ (e: List[Exp]) =>
            (Seq(ContExp(listBuilder(e), listF.assignmentsAsOriginals), ContExp(lambda)), Cont())
          }
        case Var(v) => // Convert to a formula and return a new variable
          newOutputProgram.getFunctionValue match {
            case Some(ListLiteral(newOutputList, _)) =>
              filterRev(originalInput, filterLambda, newOutputList).map{ (e: List[Exp]) =>
                (Seq(ContExp(listBuilder(e), listF.assignmentsAsOriginals), ContExp(lambda)), Cont())
              }
            case _ =>
              val newVar = freshen(v)
              Stream(((Seq(ContExp(newVar), ContExp(lambda)),
                newOutputProgram.context combineWith listF.assignmentsAsOriginals combineWith Cont(Map(), builder(Seq(newVar, lambda)) === newOutput))))
          }

        case _ => ???
      }
    }
  }
}
