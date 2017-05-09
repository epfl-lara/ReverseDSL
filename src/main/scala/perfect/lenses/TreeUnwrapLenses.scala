package perfect.lenses
import inox.{FreshIdentifier, Identifier}
import perfect.InoxProgramUpdater
import perfect.semanticlenses.TreeWrap
import inox.trees.{Application, Lambda, Let}

/**
  * Created by Mikael on 09/05/2017.
  */
trait TreeUnwrapLenses { self: InoxProgramUpdater.type =>
  import inox.trees.{ADT, ADTType, ADTConstructor}

  object TreeUnwrapLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case TreeUnwrapGoal(tpe, original, l) =>
          l match {
            case Nil => Stream(in.assignmentsAsOriginals())
            case head :: tail =>
              in.exp match {
                case l@ADT(ADTType(adtid, tps), args) =>
                  symbols.adts(adtid) match {
                    case f: ADTConstructor =>
                      val i = f.selectorID2Index(head)
                      return repair(in.subExpr(args(i)), out.subExpr(TreeUnwrapGoal(tpe, args(i), tail)))
                    case _ => Stream.empty
                  }
                case _ => Stream.empty
              }
          }
        case _ => Stream.empty
      }
    }
    isPreemptive = true
  }
}

object TreeUnwrapGoal extends FunDefGoal {
  import inox._
  import inox.trees._
  import inox.trees.dsl._

  private val Unwrap = FreshIdentifier("unwrap")

  def apply(tpe: Type, original: Expr, argsInSequence: List[Identifier]): Expr = {
    E(Unwrap)(tpe)(original, Select(tpe, argsInSequence))
  }
  def unapply(e: Expr): Option[(Type, Expr, List[Identifier])] = {
    e match {
      case FunctionInvocation(Unwrap, Seq(tpe), Seq(original, Lambda(Seq(unwrapvd), adtselectors))) =>
        def unbuild(e: Expr): (Type, Expr, List[Identifier]) = e match {
          case ADTSelector(e, i) =>
            val (t, res, l) = unbuild(e)
            (t, res, l :+ i)
          case res => (tpe, original, Nil)
        }
        Some(unbuild(adtselectors))
      case _ => None
    }
  }


  /** Builds and Unbuilds a lambda to select parts of the expression */
  object Select {
    def apply(tpe: Type, argsInSequence: List[Identifier]): Expr = {
      \("original"::tpe)(original =>
        ((original: Expr) /: argsInSequence){ case (e, i) => ADTSelector(e, i)}
      )
    }
    def unapply(e: Expr): Option[(Type, List[Identifier])] = {
      e match {
        case Lambda(Seq(ValDef(_, tpe, _)), body) =>
          def unbuild(e: Expr): Option[(Type, List[Identifier])] = e match {
            case ADTSelector(e, i) => unbuild(e) map { case (t, l) => (t, l :+ i) }
            case v: Variable => Some((tpe, Nil))
            case _ => None
          }
          unbuild(body)
        case _ => None
      }
    }
  }

  def funDef = mkFunDef(Unwrap)("A"){ case Seq(tA) =>
    (Seq("original"::tA, "unwrapper"::FunctionType(Seq(tA), tA)),
      tA, {
      case Seq(original, unwrapper) =>
        Application(unwrapper, Seq(original))
    })
  }
}