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
    def unapply(e: Exp): Option[(Exp, Exp, List[Exp] => Exp)]
  }
}
