package perfect.lenses

import perfect.InoxProgramUpdater
import perfect.core.predef.{TreeModificationLenses, TreeUnwrapLenses}

/**
  * Created by Mikael on 09/05/2017.
  */
trait ShapeLenses
  extends perfect.lenses.TreeWrapLenses
  with TreeUnwrapLenses
  with TreeModificationLenses { self: InoxProgramUpdater.type =>
}
