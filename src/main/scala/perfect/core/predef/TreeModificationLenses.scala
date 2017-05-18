package perfect.core
package predef

/**
  * Created by Mikael on 09/05/2017.
  */
trait TreeModificationLenses {  self: ProgramUpdater with
  ContExps with Lenses with ADTLenses =>

  /** Returns a lambda, the modified subtree, and an index indicating where the next change should happen with the new subgoal */
  def extractTreeModificationGoal(e: Exp)(implicit symbols: Symbols):
    Option[(Exp, Int)]

  /** Returns a goal with the modified tree, and the index where the modification occurred..*/
  def buildTreeModificationGoal(original: Exp, modified: Exp, index: Int)(implicit symbols: Symbols): Exp

  object TreeModificationLensGoal {
    def unapply(e: Exp)(implicit symbols: Symbols): Option[(Exp, Int)]= extractTreeModificationGoal(e)
    def apply(original: Exp, modified: Exp, index: Int)(implicit symbols: Symbols): Exp = buildTreeModificationGoal(original, modified, index)
  }

  object TreeModificationLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case TreeModificationLensGoal(modified, index) =>
          in.exp match {
            case l@ADT(args, adtBuilder) =>
              for {pf <- repair(in.subExpr(args(index)),
                out.subExpr(modified))} yield {
                pf.wrap(x => adtBuilder(args.take(index) ++ List(x) ++ args.drop(index + 1)))
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
        case _ => Stream.empty
      }
    }
  }
}


