package perfect.core
package predef

/**
  * Created by Mikael on 16/05/2017.
  */

trait RecursiveLenses extends RecursiveLensesLike {
  self: ProgramUpdater
    with ContExps with Lenses with LambdaLenses with InvocationLenses with ApplicationLenses =>

  object RecursiveLens2 extends RecursiveLens2Like(ApplicationExtractor, LambdaExtractor, InvocationExtractor)
}


