package perfect.core
package predef


/**
  * Created by Mikael on 09/05/2017.
  */

trait ListLenses extends ListLensesLike { self: ProgramUpdater =>
  /** Returns the elements and a builder to build back the list. */
  def extractList(e: Exp): Option[(List[Exp], List[Exp] => Exp)]

  /** Extracts a non-empty list (from an ADT from example) */
  def extractCons(e: Exp): Option[(Exp, Exp, List[Exp] => Exp)]

  object ListLiteral extends ListLiteralExtractor {
    def unapply(e: Exp): Option[(List[Exp], List[Exp] => Exp)] = extractList(e)
  }

  object Cons extends ListConsExtractor {
    def unapply(e: Exp) = extractCons((e))
  }
}


