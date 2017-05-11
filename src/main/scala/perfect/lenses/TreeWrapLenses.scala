package perfect.lenses
import inox.FreshIdentifier
import perfect.InoxProgramUpdater
import perfect.semanticlenses.{TreeWrapGoal, TreeWrap}
import inox.trees.{Application, Lambda, Let}

/**
  * Created by Mikael on 09/05/2017.
  */
trait TreeWrapLenses { self: InoxProgramUpdater.type =>
  object TreeWrapLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case TreeWrapGoal(original, wrapper) if in.canDoWrapping =>
          in.exp match {
            case l: Let => Stream.empty
            case Application(Lambda(_, _), _) => Stream.empty
            case _ => Stream(ContExp(wrapper(in.exp), out.context))
          }
        case _ => Stream.empty
      }
    }
    isPreemptive = true
  }
}



