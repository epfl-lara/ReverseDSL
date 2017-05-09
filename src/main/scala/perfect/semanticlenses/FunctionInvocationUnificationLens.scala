package perfect
package semanticlenses

import inox.trees._
import perfect.{ProgramFormula, ReverseProgram}
import perfect.ReverseProgram.Cache

/**
  * Created by Mikael on 09/05/2017.
  */
object FunctionInvocationUnificationLens extends SemanticLens {
  def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    out.expr match {
      case FunctionInvocation(f2, tpes2, args2) =>
        in.expr match {
          case FunctionInvocation(f, tpes, args) if f == f2 && tpes == tpes2 =>
            val argsRepaired = args.zip(args2) map {
              case (a1, a2) => ReverseProgram.repair(in.subExpr(a1), out.subExpr(a2))
            }
            for(psf <- ProgramFormula.regroupArguments(argsRepaired)) yield {
              ProgramFormula(FunctionInvocation(`f`, tpes, psf._1), psf._2)
            }
          case _ => Stream.empty
        }
      case _ => Stream.empty
    }
  }
  isPreemptive = false
}
