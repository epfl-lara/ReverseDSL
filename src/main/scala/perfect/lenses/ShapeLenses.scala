package perfect.lenses

import perfect.InoxProgramUpdater

/**
  * Created by Mikael on 09/05/2017.
  */
trait ShapeLenses
  extends perfect.lenses.TreeWrapLenses
  with perfect.lenses.TreeUnwrapLenses
  with perfect.lenses.TreeModificationLenses { self: InoxProgramUpdater.type =>
}
