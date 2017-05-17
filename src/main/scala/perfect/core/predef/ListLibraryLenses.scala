package perfect.core
package predef


/**
  * Created by Mikael on 10/05/2017.
  */
trait ListLibraryLenses extends ListLibraryLensesLike { self: ProgramUpdater
  with ContExps with Lenses with ListLenses with ListInsertLenses with InvocationLenses with ApplicationLenses =>

  /** In a map, can the output be transfered to the input, e.g. when adding a new row.*/
  def canPushInsertedOutputToInput(output: Exp, lambda: Exp)(implicit symbols: Symbols): Boolean
  /** Returns an expression, the default value matching the first lambda argument's type */
  def extractLambdaDefaultArgument(e: Exp): Option[Exp]
  /** Returns an "unknown" fresh variable matching the type of the lambda's first argument*/
  def extractLambdaUnknownVar(e: Exp): Option[Var]

  object ListLibraryOptions extends ListLibraryOptions {
    /** In a map, can the output be transfered to the input, e.g. when adding a new row.*/
    def canPushInsertedOutputToInput(output: Exp, lambda: Exp)(implicit symbols: Symbols): Boolean = self.canPushInsertedOutputToInput(output, lambda)
    /** Returns an expression, the default value matching the first lambda argument's type */
    def extractLambdaDefaultArgument(e: Exp): Option[Exp] = self.extractLambdaDefaultArgument(e)
    /** Returns an "unknown" fresh variable matching the type of the lambda's first argument*/
    def extractLambdaUnknownVar(e: Exp): Option[Var] = self.extractLambdaUnknownVar(e)
  }

  object FilterLens extends FilterLensLike(ApplicationExtractor, InvocationExtractor, ListLiteral, ListLibraryOptions)

  object MapLens extends MapLensLike(ApplicationExtractor, InvocationExtractor, ListLiteral, ListInsertLensGoal, ListLibraryOptions)

  object FlatMapLens extends FlatMapLensLike(ApplicationExtractor, InvocationExtractor, ListLiteral, ListInsertLensGoal, ListLibraryOptions)
}




