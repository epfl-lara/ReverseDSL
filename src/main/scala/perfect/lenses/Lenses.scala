package perfect
package lenses

import inox.Identifier
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._

trait Lenses { self: ReverseProgram.type =>
  import Utils._

  val reversers = List[Reverser](
    FilterReverser,
    MapReverser,
    ListConcatReverser,
    FlattenReverser,
    FlatMapReverser,
    StringConcatReverser
  )

  val reversions = reversers.map(x => x.identifier -> x).toMap
  val funDefs = reversers.map(_.funDef)

  abstract class Reverser {
    def identifier: Identifier
    def funDef: FunDef
    def mapping = identifier -> this
    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: Expr)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[Expr], Formula)]
  }

  object ListLiteral {
    def unapply(e: Expr): Option[List[Expr]] = e match {
      case ADT(ADTType(Utils.cons, tps), Seq(head, tail)) =>
        unapply(tail).map(head :: _ )
      case ADT(ADTType(Utils.nil, tps), Seq()) =>
        Some(Nil)
      case _ => None
    }
    def apply(e: List[Expr], tps: Seq[Type]): Expr = e match {
      case head :: tail =>
        ADT(ADTType(Utils.cons, tps), Seq(head, apply(tail, tps)))
      case Nil =>
        ADT(ADTType(Utils.nil, tps), Seq())
    }
  }

  /** Lense-like filter */
  case object FilterReverser extends Reverser with FilterLike[Expr] { // TODO: Incorporate filterRev as part of the sources.
    val identifier = Utils.filter
    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: Expr)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[Expr], Formula)] = {
      val lambda = originalArgsValues.tail.head
      val ListLiteral(originalInput) = originalArgsValues.head
      //Log(s"Reversing $originalArgs: $originalOutput => $newOutput")
      filterRev(originalInput, (expr: Expr) => evalWithCache(Application(lambda, Seq(expr))) == BooleanLiteral(true), ListLiteral.unapply(newOutput).get).map{ (e: List[Expr]) =>
        (Seq(ListLiteral(e, tpes), lambda), Formula())
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
      val ListLiteral(originalInput) = originalArgsValues.head
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
            case ProgramFormula(Application(_, Seq(in2)), Formula(mapping, _, _))
              if in2 != in => //The argument's values have changed
              Stream(Left(in))
            case ProgramFormula(Application(_, Seq(in2)), f@Formula(mapping, _, _))
              if in2 == in && in2.isInstanceOf[Variable] =>
              // The repair introduced a variable. We evaluate all possible values.
              // TODO: Alternatively, propagate the constraint on the variable
              f.evalPossible(in2).map(Left(_))
            case e@ProgramFormula(Application(lambda2: Lambda, Seq(in2)), f@Formula(mapping, _, _))
              if in2 == in && lambda2 != lambda => // The lambda has changed.
              f.evalPossible(lambda2).map(lambda => Right((in, castOrFail[Expr, Lambda](lambda))))
            case e@ProgramFormula(app, f) =>
              throw new Exception(s"Don't know how to invert both the lambda and the value: $e")
          }.filter(_ != Left(StringLiteral(uniqueString)))
        }
      }

      //Log(s"Reversing $originalArgs: $originalOutput => $newOutput")
      mapr.mapRev(originalInput, ListLiteral.unapply(newOutput).get).flatMap{
        (e: List[Either[Expr, (Expr, Lambda)]]) =>
        //Log("Final solution : " + e)
        val argumentsChanged = e.map{
          case Left(e) => e
          case Right((e, lambda)) => e
        }
        val newLambdas = if(e.exists(_.isInstanceOf[Right[_, _]])) {
          e.collect{ case Right((expr, lambda: Lambda)) => lambda }.toStream
        } else Stream(lambda)
        for(l <- newLambdas) yield {
          (Seq(ListLiteral(argumentsChanged, tpes.take(1)), l), Formula())
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

  /** Lense-like map, with the possibility of changing the mapping lambda. */
  case object FlattenReverser extends Reverser {
    val identifier = Utils.flatten

    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: Expr)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[Expr], Formula)] = {
      ???
    }

    // Flatten definition in inox
    val funDef = mkFunDef(identifier)("A"){ case Seq(tA) =>
      (Seq("ls" :: T(Utils.list)(T(Utils.list)(tA))),
        T(Utils.list)(tA),
        { case Seq(ls) =>
          if_(ls.isInstOf(T(Utils.cons)(T(Utils.list)(tA)))) {
            let("c"::T(Utils.cons)(T(Utils.list)(tA)), ls.asInstOf(T(Utils.cons)(T(Utils.list)(tA))))(c =>
              let("head"::T(Utils.list)(tA), c.getField(Utils.head))( head =>
                FunctionInvocation(Utils.listconcat, Seq(tA), Seq(head,
                  FunctionInvocation(identifier, Seq(tA), Seq(c.getField(Utils.tail)))
                ))
              )
            )
          } else_ {
            ADT(T(Utils.nil)(T(Utils.list)(tA)), Seq())
          }
        })
    }
  }

  /** Lense-like map, with the possibility of changing the mapping lambda. */
  case object FlatMapReverser extends Reverser {
    val identifier = Utils.flatmap

    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: Expr)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[Expr], Formula)] = {
      ???
    }

    // Flatmap definition in inox
    val funDef = mkFunDef(identifier)("A", "B"){ case Seq(tA, tB) =>
      (Seq("ls" :: T(Utils.list)(tA), "f" :: FunctionType(Seq(tA), T(Utils.list)(tB))),
        T(Utils.list)(tB),
        { case Seq(ls, f) =>
          if_(ls.isInstOf(T(Utils.cons)(tA))) {
            let("c"::T(Utils.cons)(tA), ls.asInstOf(T(Utils.cons)(tA)))(c =>
              let("headMapped"::T(Utils.list)(tB), f(c.getField(Utils.head)))( headMapped =>
                E(Utils.listconcat)(headMapped, E(identifier)(tA, tB)(c.getField(Utils.tail), f))
              )
            )
          } else_ {
            ADT(T(Utils.nil)(tB), Seq())
          }
        })
    }
  }


  /** Lense-like list concat, with the possibility of changing the mapping lambda. */
  case object ListConcatReverser extends Reverser {
    val identifier = Utils.listconcat

    def startsWith(list: Expr, beginning: Expr): Boolean = (list, beginning) match {
      case (ADT(_, Seq(head, tail)), ADT(_, Seq())) => true
      case (ADT(_, Seq(head, tail)), ADT(_, Seq(head2, tail2))) =>
        head == head2 && startsWith(tail, tail2)
      case _ => false
    }

    def reverse(list: Expr, gather: Option[Expr]): Expr = list match {
      case ADT(tpe@ADTType(c, targs), Seq(head, tail)) =>
        val gathertail = gather.getOrElse(ADT(ADTType(Utils.nil, targs), Seq()))
        reverse(tail, Some(ADT(tpe, Seq(head, gathertail))))
      case ADT(_, Seq()) => gather.getOrElse(list)
    }

    def endsWith(list: Expr, end: Expr): Boolean = startsWith(reverse(list, None), reverse(end, None))

    def put(tps: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: Expr)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[Expr], Formula)] = {
      val leftValue = originalArgsValues.head
      val rightValue = originalArgsValues.tail.head

      def defaultCase: Stream[(Seq[Expr], Formula)] = {
        val left = ValDef(FreshIdentifier("l", true), T(Utils.list)(tps.head), Set())
        val right = ValDef(FreshIdentifier("r", true), T(Utils.list)(tps.head), Set())
        Log(s"List default case: ${left.id} + ${right.id} == $newOutput")

        val f = Formula(Map(), Set(),
          newOutput === FunctionInvocation(Utils.listconcat, tps, Seq(left.toVariable, right.toVariable)) &&
          not(left.toVariable === leftValue) && not(right.toVariable === rightValue)
        )

        Stream((Seq(left.toVariable, right.toVariable), f))
      }

      // Prioritize changes that touch only one of the two expressions.
      newOutput match {
        case ListLiteral(s) =>
          (leftValue match {
            case ListLiteral(lv) =>
              if (s.startsWith(lv)) {
                Stream((Seq(leftValue, ListLiteral(s.drop(lv.length), tps)), Formula()))
              } else Stream.empty
            case _ => Stream.empty
          }) #::: (
            rightValue match {
              case ListLiteral(rv) =>
                if (s.endsWith(rv)) {
                  Stream((Seq(ListLiteral(s.take(s.length - rv.length), tps), rightValue), Formula()))
                } else Stream.empty
              case _ => Stream.empty
            }
            ) #::: defaultCase
        case newOut: Variable => defaultCase

        case l@Let(vd, value, newbody) =>
          /* Copy and paste, insertion, replacement:
        *  => A single let(v, newText, newbody) with a single occurrence of v in newbody
        *  Clone and paste
        *  => A double let(clone, oldText, let(paste, clone, newbody)) with two occurrences of clone in newbody
        *  Cut and paste
        *  => A double let(cut, "", let(paste, clone, newbody)) with one occurrences of paste in newbody
        *  Delete
        *  => A single let(delete, "", newbody) with a single occurrence of delete in newbody
        **/
          ???
      }
    }

    // Concat definition in inox
    val funDef = mkFunDef(identifier)("A"){ case Seq(tA) =>
      (Seq("left" :: T(Utils.list)(tA), "right" :: T(Utils.list)(tA)),
        T(Utils.list)(tA),
        { case Seq(left, right) =>
          if_(left.isInstOf(T(Utils.cons)(tA))) {
            let("c"::T(Utils.cons)(tA), left.asInstOf(T(Utils.cons)(tA)))(c =>
              ADT(T(Utils.cons)(tA),
                Seq(c.getField(Utils.head), E(identifier)(tA)(c.getField(Utils.tail), right)))
            )
          } else_ {
            right
          }
        })
    }
  }

  /** Lense-like list concat, with the possibility of changing the mapping lambda. */
  case object StringConcatReverser extends Reverser {
    val identifier = FreshIdentifier("tmpstringconcat")

    def put(tps: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: Expr)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[Expr], Formula)] = {
      val leftValue = originalArgsValues.head
      val rightValue = originalArgsValues.tail.head

      def leftCase(s: String):  Stream[(Seq[Expr], Formula)] = {
        Log.prefix("Testing left:") := (leftValue match {
          case StringLiteral(lv) =>
            (if (s.startsWith(lv)) {
              Stream((Seq(leftValue, StringLiteral(s.drop(lv.length))), Formula()))
            } else Stream.empty) /:: Log.prefix("Left worked:")
          case _ => Stream.empty
        })
      }

      def rightCase(s: String): Stream[(Seq[Expr], Formula)] = {
        Log.prefix("Testing right:") := (rightValue match {
          case StringLiteral(rv) =>
            (if (s.endsWith(rv)) {
              Stream((Seq(StringLiteral(s.take(s.length - rv.length)), rightValue), Formula()))
            } else Stream.empty)  /:: Log.prefix("right worked:")
          case _ => Stream.empty
        })
      }

      def defaultCase(addMaybes: Boolean = false): Stream[(Seq[Expr], Formula)] = {
        val left = ValDef(FreshIdentifier("l", true), StringType, Set())
        val right = ValDef(FreshIdentifier("r", true), StringType, Set())
        Log(s"String default case: ${left.id} + ${right.id} == $newOutput:")

        val newConstraint = (newOutput === FunctionInvocation(identifier, tps, Seq(left.toVariable, right.toVariable))
        &<>& (if(addMaybes)
          E(Utils.maybe)(left.toVariable === leftValue) && E(Utils.maybe)(right.toVariable === rightValue)
        else BooleanLiteral(true)
        ) // Maybe use what is below for faster convergence?
        //            (if(addMaybes) not(left.toVariable === leftValue) && not(right.toVariable === rightValue)
          )
        val newVarsInConstraint = exprOps.variablesOf(newConstraint).map(_.toVal)
        val f = Formula(unknownConstraints = newConstraint)

        Stream((Seq(left.toVariable, right.toVariable), f))
      }

      // Prioritize changes that touch only one of the two expressions.
      newOutput match {
        case StringLiteral(s) =>
          rightCase(s) append leftCase(s) append {
            defaultCase(false)
          }
        case l@Let(vd, value, newbody) =>
          /* Copy and paste, insertion, replacement:
        *  => A single let(v, newText, newbody) with a single occurrence of v in newbody
        *  Clone and paste
        *  => A double let(clone, oldText, let(paste, clone, newbody)) with two occurrences of clone in newbody
        *  Cut and paste
        *  => A double let(cut, "", let(paste, clone, newbody)) with one occurrences of paste in newbody
        *  Delete
        *  => A single let(delete, "", newbody) with a single occurrence of delete in newbody
        **/
          ???
        case _ =>
          defaultCase(true)
      }
    }

    // Concat definition in inox
    val funDef = mkFunDef(identifier)(){ case _ =>
      (Seq("a" :: StringType, "b" :: StringType),
        StringType,
        { case Seq(left, right) =>
          StringConcat(left, right)
        })
    }
  }
}
