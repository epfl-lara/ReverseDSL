package perfect.core
package predef

/**
  * Created by Mikael on 15/05/2017.
  */
trait ListLensesLike { self: ProgramUpdater =>
  trait ListLiteralExtractor {
    def unapply(e: Exp): Option[(List[Exp], List[Exp] => Exp)]
  }
  trait ListConsExtractor {
    /** Returns the head, the tail of the list and a way to build a list from scratch*/
    def unapply(e: Exp): Option[(Exp, Exp, List[Exp] => Exp)]
  }
}
