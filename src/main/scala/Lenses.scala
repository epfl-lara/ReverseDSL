/**
  * Created by Mikael on 15/03/2017.
  */
import inox._
import inox.trees._
import inox.trees.dsl._


trait Lenses { self: ReverseProgram.type =>
  import Utils._

  val reversers = List[Reverser](
    FilterReverser,
    MapReverser
  )

  val reversions = reversers.map(x => x.identifier -> x).toMap
  val funDefs = reversers.map(_.funDef)

  abstract class Reverser {
    def identifier: Identifier
    def funDef: FunDef
    def mapping = identifier -> this
    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: Expr)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[Expr], Formula)]
  }

  // Todo: Move to utils or somewhere else.
  def unwrapList(e: Expr): List[Expr] = e match {
    case ADT(ADTType(Utils.cons, tps), Seq(head, tail)) =>
      head :: unwrapList(tail)
    case ADT(ADTType(Utils.nil, tps), Seq()) =>
      Nil
  }
  def wrapList(e: List[Expr], tps: Seq[Type]): Expr = e match {
    case head :: tail =>
      ADT(ADTType(Utils.cons, tps), Seq(head, wrapList(tail, tps)))
    case Nil =>
      ADT(ADTType(Utils.nil, tps), Seq())
  }

  /** Lense-like filter */
  case object FilterReverser extends Reverser with FilterLike[Expr] { // TODO: Incorporate filterRev as part of the sources.
    val identifier = Utils.filter
    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: Expr)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[Expr], Formula)] = {
      val lambda = originalArgsValues.tail.head
      val originalInput = originalArgsValues.head
      //Log(s"Reversing $originalArgs: $originalOutput => $newOutput")
      filterRev(unwrapList(originalInput), (expr: Expr) => evalWithCache(Application(lambda, Seq(expr))) == BooleanLiteral(true), unwrapList(newOutput)).map{ (e: List[Expr]) =>
        (Seq(wrapList(e, tpes), lambda), Formula())
      }
    }

    // filter definition in inox
    val funDef = mkFunDef(identifier)("A"){ case Seq(tp) =>
      (Seq("ls" :: T(Utils.list)(tp), "f" :: FunctionType(Seq(tp), BooleanType)),
        T(Utils.list)(tp),
        { case Seq(ls, f) =>
          if_(ls.isInstOf(T(Utils.cons)(tp))) {
            let("c"::T(Utils.cons)(tp), ls.asInstOf(T(Utils.cons)(tp)))(c =>
              let("head"::tp, c.getField(Utils.head))( head =>
                if_(Application(f, Seq(head))){
                  ADT(T(Utils.cons)(tp), Seq(head, E(identifier)(tp)(c.getField(Utils.tail), f)))
                } else_ {
                  E(identifier)(tp)(c.getField(Utils.tail), f)
                }
              )
            )
          } else_ {
            ADT(T(Utils.nil)(tp), Seq())
          }
        })
    }
  }

  /** Lense-like map, with the possibility of changing the mapping lambda. */
  case object MapReverser extends Reverser {
    val identifier = Utils.map

    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: Expr)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[Expr], Formula)] = {
      Log(s"map.apply($newOutput)")
      val lambda = castOrFail[Expr, Lambda](originalArgsValues.tail.head)
      val originalInput = originalArgsValues.head
      val uniqueString = "_"
      // Maybe we change only arguments. If not possible, we will try to change the lambda.
      val mapr = new MapReverseLike[Expr, Expr, (Expr, Lambda)] {
        override def f = (expr: Expr) => evalWithCache(Application(lambda, Seq(expr)))

        override def fRev = (prevIn: Option[Expr], out: Expr) => {
          Log(s"fRev: $prevIn, $out")
          val (Seq(in), newFormula) =
            prevIn.map(x => (Seq(x), Formula(Map[ValDef, Expr]()))).getOrElse {
              val unknown = ValDef(FreshIdentifier("unknown"),lambda.args.head.getType)
              (Seq(unknown.toVariable), Formula(Map[ValDef, Expr](unknown -> StringLiteral(uniqueString)), Set(unknown)))
            }
          Log(s"in:$in\nnewformula:$newFormula")
          Log.prefix("res=") :=
          repair(ProgramFormula(Application(lambda, Seq(in)), newFormula), out).flatMap {
            case ProgramFormula(Application(_, Seq(in2)), Formula(mapping, vtoAssign, _, _))
              if in2 != in => //The argument's values have changed
              Stream(Left(in))
            case ProgramFormula(Application(_, Seq(in2)), f@Formula(mapping, vtoAssign, _, _))
              if in2 == in && in2.isInstanceOf[Variable] =>
              // The repair introduced a variable. We evaluate all possible values.
              // TODO: Alternatively, propagate the constraint on the variable
              f.evalPossible(in2).map(Left(_))
            case e@ProgramFormula(Application(lambda2: Lambda, Seq(in2)), f@Formula(mapping, vtoAssign, _, _))
              if in2 == in && lambda2 != lambda => // The lambda has changed.
              f.evalPossible(lambda2).map(lambda => Right((in, castOrFail[Expr, Lambda](lambda))))
            case e@ProgramFormula(app, f) =>
              throw new Exception(s"Don't know how to invert both the lambda and the value: $e")
          }.filter(_ != Left(StringLiteral(uniqueString)))
        }
      }

      //Log(s"Reversing $originalArgs: $originalOutput => $newOutput")
      mapr.mapRev(unwrapList(originalInput), unwrapList(newOutput)).flatMap{ (e: List[Either[Expr, (Expr, Lambda)]]) =>
        //Log("Final solution : " + e)
        val argumentsChanged = e.map{
          case Left(e) => e
          case Right((e, lambda)) => e
        }
        val newLambdas = if(e.exists(_.isInstanceOf[Right[_, _]])) {
          e.collect{ case Right((expr, lambda: Lambda)) => lambda }.toStream
        } else Stream(lambda)
        for(l <- newLambdas) yield {
          (Seq(wrapList(argumentsChanged, tpes.take(1)), l), Formula())
        }
      }
    }

    // Map definition in inox
    val funDef = mkFunDef(identifier)("A", "B"){ case Seq(tA, tB) =>
      (Seq("ls" :: T(Utils.list)(tA), "f" :: FunctionType(Seq(tA), tB)),
        T(Utils.list)(tB),
        { case Seq(ls, f) =>
          if_(ls.isInstOf(T(Utils.cons)(tA))) {
            let("c"::T(Utils.cons)(tA), ls.asInstOf(T(Utils.cons)(tA)))(c =>
              let("head"::tA, c.getField(Utils.head))( head =>
                ADT(T(Utils.cons)(tB), Seq(Application(f, Seq(head)), E(identifier)(tA, tB)(c.getField(Utils.tail), f)))
              )
            )
          } else_ {
            ADT(T(Utils.nil)(tB), Seq())
          }
        })
    }
  }
}
