package perfect.core
package predef

/**
  * Created by Mikael on 15/05/2017.
  */
trait UnificationLensesLike { self: ProgramUpdater with ContExps with Lenses with InvocationLensesLike =>
  class FunctionInvocationUnificationLensLike(Invocation: InvocationExtractor) extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.exp match {
        case Invocation(args2, builder) =>
          in.exp match {
            case Invocation(args, _) if Invocation.isSame(out.exp, in.exp) =>
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
