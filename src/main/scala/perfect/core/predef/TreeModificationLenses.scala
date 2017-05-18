package perfect.core
package predef

/**
  * Created by Mikael on 09/05/2017.
  */
trait TreeModificationLenses {  self: ProgramUpdater with
  ContExps with Lenses with ADTLenses =>

  /** Returns the original tree, the modified subtree, and instead of a path,
    * an index indicating where the next change should happen with the new subgoal */
  def extractTreeModificationGoal(e: Exp)(implicit symbols: Symbols):
    Option[(Exp, Exp, Option[(Int, Exp)])]

  /** Returns a goal with the original tree, the modified tree, and the next path element.
    * The second exp of the path element should continue with TreeMdodificationGoal until the modified
    * part of the original is reached. */
  def buildTreeModificationGoal(original: Exp, modified: Exp, path: Option[(Int, Exp)])(implicit symbols: Symbols): Exp

  object TreeModificationLensGoal {
    def unapply(e: Exp)(implicit symbols: Symbols): Option[(Exp, Exp, Option[(Int, Exp)])] = extractTreeModificationGoal(e)
    def apply(original: Exp, modified: Exp, path: Option[(Int, Exp)])(implicit symbols: Symbols): Exp = buildTreeModificationGoal(original, modified, path)
  }

  object TreeModificationLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case TreeModificationLensGoal(original, modified, l) =>
          l match {
            case None =>
              repair(in, out.subExpr(modified))
            case Some((index, treeModificationlensGoal)) =>
              in.exp match {
                case l@ADT(args, adtBuilder) =>
                  original match {
                    case ADT(argsOriginal, _) =>
                      val subOriginal = argsOriginal(index)
                      for {pf <- repair(in.subExpr(args(index)),
                        out.subExpr(treeModificationlensGoal))} yield {
                        pf.wrap(x => adtBuilder(args.take(index) ++ List(x) ++ args.drop(index + 1)))
                      }
                  }
                /*case TreeModification.Goal(tpeGlobal, tpeLocal, original@ADT(adt, Seq(hdOriginal, tlOriginal)), modified, path) =>
                  val (index, remaining) = path.span(_ == Utils.tail)
                  leftValue match {
                    case ListLiteral(l, _) =>
                      if(index.length < l.length) {
                        Stream((Seq(
                          TreeModification(tpeGlobal, tpeLocal, original, modified, path),
                          ContExp(rightValue)),
                          Cont())
                        )
                      } else {
                        Stream((Seq(
                          ContExp(leftValue),
                          TreeModification(tpeGlobal, tpeLocal, original, modified, path.drop(index.length))),
                          Cont()
                        ))
                      }
                    case _ => Stream.empty
                  }*/
                case _ => Stream.empty
              }
          }
        case _ => Stream.empty
      }
    }
  }
}


