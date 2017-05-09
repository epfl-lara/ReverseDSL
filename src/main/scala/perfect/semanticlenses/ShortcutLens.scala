package perfect.semanticlenses
import inox.trees._
import perfect.ProgramFormula
import perfect.ReverseProgram.Cache

/**
  * Created by Mikael on 09/05/2017.
  * Wrapper around a set of indexable lenses to quickly reach them.
  */
case class ShortcutLens[A](map: Map[A, SemanticLens], f: Expr => Option[A]) extends SemanticLens {
  override def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    f(in.expr) match {
      case Some(a) => map.get(a) match {
        case Some(lens) => lens.put(in, out)
        case _ => Stream.empty
      }
      case _ => Stream.empty
    }
  }
}