package perfect.core
package predef


/**
  * Created by Mikael on 10/05/2017.
  */
trait UnificationLenses { self: ProgramUpdater with ContExps with Lenses with InvocationLenses =>
  def isSameInvocation(e1: Exp, e2: Exp)(implicit cache: Cache, symbols: Symbols): Boolean

  object FunctionInvocationUnificationLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      extractInvocation(out.exp) match {
        case Some((args2, builder)) =>
          extractInvocation(in.exp) match {
            case Some((args, _)) if isSameInvocation(out.exp, in.exp) =>
              val argsRepaired = args.zip(args2) map {
                case (a1, a2) => repair(in.subExpr(a1), out.subExpr(a2))
              }
              for(psf <- ContExp.regroupArguments(argsRepaired)) yield {
                ContExp(builder(psf._1), psf._2)
              }
            case _ => Stream.empty
          }
        case _ => Stream.empty
      }
    }
    isPreemptive = false
  }
}
