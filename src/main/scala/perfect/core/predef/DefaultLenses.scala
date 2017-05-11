package perfect.core.predef

import perfect.core._

trait DefaultLenses extends LambdaLenses
  with VariableLenses with LetLenses with ApplicationLenses with IfLenses with AsInstanceOfLenses {
  self: ProgramUpdater with ContExps with Lenses =>

  def defaultLens = combine(
    LambdaLens,
    VariableLens,
    LetLens,
    ApplicationLens,
    IfLens,
    AsInstanceOfLens
  )
}
