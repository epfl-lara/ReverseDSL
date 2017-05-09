package perfect.core
package predef

/**
  * Created by Mikael on 09/05/2017.
  */
trait InvocationLenses { self: ProgramUpdater with ContExps =>
  def extractInvocation(e: Exp)(implicit cache: Cache, symbols: Symbols):
  Option[( Seq[Exp], Seq[Exp] => Exp )]
}
