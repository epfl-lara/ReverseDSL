package perfect.core
package predef

/**
  * Created by Mikael on 16/05/2017.
  */
trait RecursiveLensesLike { self: ProgramUpdater
  with ContExps with Lenses with LambdaLensesLike with InvocationLensesLike with ApplicationLensesLike =>


  /*class RecLens(Lambda: LambdaExtractor) {
    def build(name: String, arg1: Var, arg2: Var)(f: (Var, Var, Var) => Exp)(implicit symbols: Symbols): Exp = {
      Lambda(Seq(arg1, arg2),
        E(RecLens2.identifier)(arg1.tpe, arg2.tpe, returnType)(
          \(name::FunctionType(Seq(arg1.tpe, arg2.tpe), returnType), "a1"::arg1.tpe, "a2"::arg2.tpe)((m, a1, a2) =>
            f(m, a1, a2)),
          arg1,
          arg2
        ))
    }
  }*/

  class RecursiveLens2Like(Application: ApplicationExtractor,
                           Lambda: LambdaExtractor,
                           Invocation: InvocationExtractor) extends InvocationLensLike(Invocation) {

    def put(originalArgValues: Seq[ContExp], out: ContExp, builder: Seq[Exp] => Exp)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ContExp], Cont)] = {
      val ContExp(fexp, f_formula) = originalArgValues.head
      fexp match {
        case f@Lambda(Seq(vL, v1, v2), body) =>
          val ContExp(x1, x1_formula) = originalArgValues.tail.head
          val ContExp(x2, x2_formula) = originalArgValues.tail.tail.head
          val a1 = freshen(v1)
          val a2 = freshen(v2)
          val equivalent =
            ContExp(Application(f, Seq(Lambda(Seq(a1, a2), builder(Seq(f, a1, a2))), x1, x2)),
              f_formula combineWith x1_formula combineWith x2_formula
            )
          repair(equivalent, out).map{
            case ContExp(Application(newF, Seq(_, newA1, newA2)), context) =>
              (Seq(ContExp(newF),
                ContExp(newA1), ContExp(newA2)), context)
          }
        case _ => Stream.empty
      }
    }
  }
}
