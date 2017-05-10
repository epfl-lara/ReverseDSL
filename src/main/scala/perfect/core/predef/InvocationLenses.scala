package perfect.core
package predef

/**
  * Created by Mikael on 09/05/2017.
  */
trait InvocationLenses { self: ProgramUpdater with ContExps with Lenses =>
  def extractInvocation(e: Exp)(implicit cache: Cache, symbols: Symbols):
  Option[( Seq[Exp], Seq[Exp] => Exp )]

  /** An invocation lens defines a put method which can reason on the original values. */
  trait InvocationLens extends MultiArgsSemanticLens  {
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

    def put(originalArgValues: Seq[ContExp], out: ContExp, builder: Seq[Exp] => Exp)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ContExp], Cont)]
  }
}
