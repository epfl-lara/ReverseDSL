package perfect.core
package predef

/**
  * Created by Mikael on 15/05/2017.
  */
trait InvocationLensesLike { self: ProgramUpdater with ContExps with Lenses =>
  trait InvocationExtractor {
    def unapply(e: Exp)(implicit cache: Cache, symbols: Symbols):
    Option[(Seq[Exp], Seq[Exp] => Exp)]
  }

  /** An invocation lens defines a put method which can reason on the original values. */
  abstract class InvocationLensLike(Invocation: InvocationExtractor) extends MultiArgsSemanticLens  {
    def extract(e: Exp)(implicit cache: Cache, symbols: Symbols): Option[( Seq[Exp],
      (Seq[ContExp], ContExp) => Stream[(Seq[ContExp], Cont)],
      Seq[Exp] => Exp
      )] =
      e match {
        case Invocation(args, builder) =>
          Some((args,
            (argValues: Seq[ContExp], out: ContExp) => {
              put(argValues, out, builder)
            },
            builder
          ))

        case _ => None
      }

    def put(originalArgValues: Seq[ContExp], out: ContExp, builder: Seq[Exp] => Exp)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ContExp], Cont)]
  }
}
