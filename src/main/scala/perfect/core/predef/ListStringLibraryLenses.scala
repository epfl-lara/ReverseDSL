package perfect.core
package predef

/**
  * Created by Mikael on 16/05/2017.
  */
trait ListStringLibraryLenses extends ListStringLibraryLensesLike { self: ProgramUpdater
  with ContExps with Lenses with ListLenses with ListInsertLenses with InvocationLenses
  with ApplicationLenses with StringLenses with StringInsertLenses =>

  object MkStringLens extends MkStringLensLike(ListLiteral, ListInsertLensGoal, InvocationExtractor, StringInsertLensGoal, StringLiteral)
}
