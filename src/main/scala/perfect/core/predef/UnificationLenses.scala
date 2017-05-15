package perfect.core
package predef


/**
  * Created by Mikael on 10/05/2017.
  */

trait UnificationLenses extends UnificationLensesLike {
  self: ProgramUpdater with ContExps with Lenses with InvocationLenses =>

  object FunctionInvocationUnificationLens extends FunctionInvocationUnificationLensLike(InvocationExtractor)
}

