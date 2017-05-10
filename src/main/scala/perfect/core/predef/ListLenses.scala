package perfect.core
package predef


/**
  * Created by Mikael on 09/05/2017.
  *
  * Make sure the symbols contain the reference to the filter function taht it is mapped to.
  */
trait ListLenses { self: ProgramUpdater =>
  /** Returns the elements and a builder to build back the list. */
  def extractList(e: Exp): Option[(List[Exp], List[Exp] => Exp)]
  object ListLiteral {
    def unapply(e: Exp) = extractList(e)
  }
  def extractCons(e: Exp): Option[(Exp, Exp, List[Exp] => Exp)]
  object Cons {
    def unapply(e: Exp) = extractCons((e))
  }
}
