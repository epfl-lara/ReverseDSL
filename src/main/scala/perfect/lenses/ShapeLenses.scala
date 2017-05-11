package perfect.lenses

import perfect.InoxProgramUpdater
import perfect.core.predef.{TreeModificationLenses, TreeUnwrapLenses, TreeWrapLenses}

/**
  * Created by Mikael on 09/05/2017.
  */
trait ShapeLenses
  extends TreeWrapLenses
  with TreeUnwrapLenses
  with TreeModificationLenses { self: InoxProgramUpdater.type =>
}
