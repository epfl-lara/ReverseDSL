package perfect.core
package predef

/**
  * Created by Mikael on 05/05/2017.
  */

trait WrappedLenses extends WrappedLensesLike {
  self: ProgramUpdater with ContExps with Lenses with ADTLenses with StringLenses with LetLenses with ApplicationLenses with LambdaLenses with ListInsertLenses with StringConcatLenses with StringInsertLenses =>

  object WrappedADTLens extends WrappedADTLensLike(ADT, LetExtractor, LambdaExtractor, ApplicationExtractor, ListInsertLensGoal)

  object WrappedStringLens extends WrappedStringLensLike(StringLiteral, StringConcat, StringInsertLensGoal, LetExtractor, LambdaExtractor, ApplicationExtractor)
}
