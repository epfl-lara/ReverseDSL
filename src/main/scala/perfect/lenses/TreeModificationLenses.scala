package perfect.lenses
import inox.{FreshIdentifier, Identifier}
import perfect.InoxProgramUpdater
import perfect.semanticlenses.TreeWrap
import inox.trees._
import inox._
import inox.trees.dsl._

/**
  * Created by Mikael on 09/05/2017.
  */
trait TreeModificationLenses {  self: InoxProgramUpdater.type =>

  object TreeModificationLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      out.simplifiedExpr match {
        case TreeModificationGoal(tpeG, tpeL, original, modified, l) =>
          l match {
            case Nil =>
              repair(in, out.subExpr(modified))
            case head :: tail =>
              in.exp match {
                case l@inox.trees.ADT(ADTType(adtid, tps), args) =>
                  symbols.adts(adtid) match {
                    case f: ADTConstructor =>
                      val i = f.selectorID2Index(head)
                      original match {
                        case inox.trees.ADT(_, argsOriginal) =>
                          val subOriginal = argsOriginal(i)
                          for {pf <- repair(in.subExpr(args(i)),
                            out.subExpr(TreeModificationGoal(subOriginal.getType, tpeL, subOriginal, modified, tail)))} yield {
                            pf.wrap(x => inox.trees.ADT(l.adt, args.take(i) ++ List(x) ++ args.drop(i + 1)))
                          }
                      }
                    case _ => Stream.empty
                  }
                case _ => Stream.empty
              }
          }
        case _ => Stream.empty
      }
    }
  }
}

object TreeModificationGoal extends FunDefGoal {
  private val Modif = FreshIdentifier("modif")

  object LambdaPath {
    def apply(original: Expr, ail: List[Identifier], modified: Expr)(implicit symbols: Symbols): Option[Expr] =
      ail match {
        case Nil =>
          Some( modified )
        case head::tail =>
          original match {
            case l@ADT(ADTType(adtid, tps), args) =>
              symbols.adts(adtid) match {
                case f: ADTConstructor =>
                  val i = f.selectorID2Index(head)
                  val expectedTp = args(i).getType
                  apply(args(i), tail, modified).map{ case expr =>
                    ADT(l.adt, args.take(i) ++ List(expr) ++ args.drop(i+1))
                  }
                case _ =>
                  None
              }
          }
      }
    def apply(original: Expr, ail: List[Identifier])(implicit symbols: Symbols): Option[Expr] =
      ail match {
        case Nil =>
          Some( \("x"::original.getType)(x => x) )
        case head::tail =>
          original match {
            case l@ADT(ADTType(adtid, tps), args) =>
              symbols.adts(adtid) match {
                case f: ADTConstructor =>
                  val i = f.selectorID2Index(head)
                  val expectedTp = args(i).getType
                  apply(args(i), tail).map{ case lambda =>
                    \("x"::original.getType)(x => ADT(l.adt, args.take(i) ++ List(Application(lambda, Seq(AsInstanceOf(ADTSelector(x, head), expectedTp)))) ++ args.drop(i+1)))
                  }
                case _ =>
                  None
              }
          }
      }
    def unapply(lambda: Expr)(implicit symbols: Symbols): Option[List[Identifier]] = lambda match {
      case Lambda(Seq(x@ValDef(_, tpe, _)), ADT(adt@ADTType(adtid, tpArgs), args)) =>
        args.zipWithIndex.collectFirst{ case (a@Application(l: Lambda, _), i) => (l, i) } flatMap {
          case (newLambda, index) =>
            symbols.adts(adtid) match {
              case f: ADTConstructor =>
                val id: Identifier= f.fields(index).id
                unapply(newLambda).map(li => id +: li)
              case _ => None
            }
        }
      case Lambda(Seq(x), xv) if x.toVariable == xv => Some(Nil)
      case _ => None
    }
  }
  def apply(tpeGlobal: Type, tpeLocal: Type, original: Expr, modified: Expr, argsInSequence: List[Identifier])(implicit symbols: Symbols): Expr = {
    E(Modif)(tpeGlobal, tpeLocal)(
      original,
      LambdaPath(original, argsInSequence).getOrElse(throw new Exception(s"Malformed original: $original or incompatible args: $argsInSequence")),
      modified
    )
  }

  def unapply(e: Expr)(implicit symbols: Symbols): Option[(Type, Type, Expr, Expr, List[Identifier])] = {
    List(e) collectFirst {
      case FunctionInvocation(Modif, Seq(tpeGlobal, tpeLocal),
      Seq(original, LambdaPath(argsInSequence), modified)) =>
        ((tpeGlobal, tpeLocal, original, modified, argsInSequence))
    }
  }

  def funDef = mkFunDef(Modif)("A", "B"){ case Seq(tA, tB) =>
    (Seq("wrapper"::FunctionType(Seq(tB), tA), "tree"::tB),
      tA, {
      case Seq(wrapper, tree) =>
        Application(wrapper, Seq(tree))
    })
  }
}
