package perfect.core
package predef

/**
  * Created by Mikael on 10/05/2017.
  */

trait MapDataLenses extends MapDataLensesLike { self: ProgramUpdater with ContExps with Lenses =>
  /** Returns the pairs, the default and a builder*/
  def extractMap(e: Exp)(implicit symbols: Symbols): Option[(Seq[(Exp, Exp)], Exp, (Seq[(Exp, Exp)], Exp) => Exp)]

  // Returns the expression building the map and the one building the argument, and a function to create a variable of type the Map's value type
  def extractMapApply(e: Exp)(implicit symbols: Symbols): Option[(Exp, Exp, String => Var)]
  def buildMapApply(e: Exp, g: Exp): Exp


  private object MapData extends MapDataExtractor {
    def unapply(e: Exp) = extractMap(e)
  }

  private object MapDataApply extends MapDataApplyExtractor {
    def unapply(e: Exp) = extractMapApply(e)

    def apply(e: Exp, g: Exp) = buildMapApply(e, g)
  }

  object MapDataLens extends MapDataLensLike(MapData, MapDataApply)
}


