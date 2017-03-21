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
    MapReverser,
    ListConcatReverser,
    FlattenReverser,
    FlatMapReverser
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
  
  /** Lense-like list concat, with the possibility of changing the mapping lambda. */
  case object ListConcatReverser extends Reverser {
    val identifier = Utils.listconcat

    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: Expr)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[Expr], Formula)] = {
      val left = originalArgsValues.head
      val right = originalArgsValues.tail.head
      ???

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

  /*trait ReverserLike[T <: Expr] {
    def unapply(pf: ProgramFormula)(implicit cache: Cache, symbols: Symbols): Option[Stream[(T, Formula)]] = {
      this.put(pf)
    }
    def put(program: ProgramFormula, newOut: Expr)(implicit cache: Cache, symbols: Symbols)
  }*/

  /*case object StringConcatReverser extends ReverserLike[StringConcat] {
    def put(program: ProgramFormula, newOut: Expr)(implicit cache: Cache, symbols: Symbols): Stream[(StringConcat, Formula)] = {
      lazy val leftValue = evalWithCache(letm(currentValues) in expr1)
      lazy val rightValue = evalWithCache(letm(currentValues) in expr2)
      lazy val finalValue = asStr(leftValue) + asStr(rightValue)

      def defaultCase: Stream[ProgramFormula] = {
        //return Stream.empty
        //Log(Thread.currentThread().getStackTrace.mkString("\n"))

        val left = ValDef(FreshIdentifier("l", true), StringType, Set())
        val right = ValDef(FreshIdentifier("r", true), StringType, Set())
        Log(s"String default case: ${left.id} + ${right.id} == $newOut")

        val leftRepair = repair(ProgramFormula(expr1, Formula(currentValues, currentValues.keySet)), left.toVariable)
        val rightRepair = repair(ProgramFormula(expr2, Formula(currentValues, currentValues.keySet)), right.toVariable)

        // TODO: JoinSet
        val bothRepair = inox.utils.StreamUtils.cartesianProduct(leftRepair, rightRepair)

        for((ProgramFormula(leftExpr, f1@Formula(mp1, varstoAssign1, unchanged1, cs1)),
        ProgramFormula(rightExpr, f2@Formula(mp2, varstoAssign2, unchanged2, cs2))) <- bothRepair) yield {
          val newCs = cs1 &<>& cs2 &<>& newOut === StringConcat(left.toVariable, right.toVariable)
          Log(s"Default case s first solution: $newCs\n${StringConcat(leftExpr, rightExpr)}")
          val conflict = (mp1.keySet intersect mp2.keySet).filter{ k => mp1(k) != mp2(k) }
          val assignmentsForSure = (mp1 ++ mp2 -- conflict)
          val newVarsToAssign =  varstoAssign1 ++ varstoAssign2 ++ Set(left, right)
          val newUnchangedVars = unchanged1 ++ unchanged2 -- newVarsToAssign
          if(conflict.nonEmpty) {
            val maybeAssignments = and(conflict.toSeq.map{ k => (k.toVariable === mp1(k) || k.toVariable === mp2(k))}: _*)
            ProgramFormula(StringConcat(leftExpr, rightExpr),
              Formula(assignmentsForSure, newVarsToAssign, newUnchangedVars, newCs &<>& maybeAssignments))
          } else {
            ProgramFormula(StringConcat(leftExpr, rightExpr),
              Formula(assignmentsForSure, newVarsToAssign, newUnchangedVars, newCs))
          }
        }
      }

      // Prioritize changes that touch only one of the two expressions.
      newOut match {
        case StringLiteral(s) =>
          (leftValue match {
            case StringLiteral(lv) =>
              if(s.startsWith(lv)) { // The left value is unchanged, let's focus on repairing the right value.
                for(ProgramFormula(rightExpr, Formula(known, varsToAssign, unchanged, unknownConstraints)) <-
                    repair(ProgramFormula(expr2, Formula(currentValues, currentValues.keySet)),
                      StringLiteral(s.substring(lv.length)))) yield {
                  val newUnknownConstraints = unknownConstraints
                  val constraintVars = exprOps.variablesOf(newUnknownConstraints).map(_.toVal)
                  val (bounded, unbounded) = (varsToAssign ++ exprOps.variablesOf(expr1).map(_.toVal) ++ unchanged).partition{ v =>
                    (known contains v) || constraintVars(v)
                  }
                  ProgramFormula(StringConcat(expr1, rightExpr),
                    Formula(known, bounded, unbounded, newUnknownConstraints)) /: Log.left_return
                }
              } else Stream.empty
            case _  => Stream.empty }) #::: (
            rightValue match {
              case StringLiteral(rv) =>
                if(s.endsWith(rv)) {
                  for(ProgramFormula(leftExpr, Formula(known, varsToAssign, unchanged, unknownConstraints))  <-
                      repair(ProgramFormula(expr1, Formula(currentValues, currentValues.keySet)),
                        StringLiteral(s.substring(0, s.length - rv.length)))) yield {
                    val newUnknownConstraints = unknownConstraints
                    val constraintVars = exprOps.variablesOf(newUnknownConstraints).map(_.toVal)
                    val (bounded, unbounded) = (varsToAssign ++ exprOps.variablesOf(expr2).map(_.toVal) ++ unchanged).partition{ v =>
                      (known contains v) || constraintVars(v)
                    }
                    ProgramFormula(StringConcat(leftExpr, expr2),
                      Formula(known, bounded, unbounded, newUnknownConstraints)) /: Log.right_return
                  }
                } else Stream.empty
              case _  => Stream.empty
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

        /*case StringConcat(a, b) => // newOut could be the concatenation with some variables
          if(b == expr2) {
            repair(expr1, currentValues, a).map(x => (StringConcat(x._1, b), x._2))
          } else if(a == expr1) {
            repair(expr2, currentValues, b).map(x => (StringConcat(a, x._1), x._2))
          } else {
            Stream((newOut, Formula(Map(), newOut === function)))
            //throw new Exception(s"Don't know how to handle $newOut for $function")
          }*/
        case _ => defaultCase
        //            case _ => throw new Exception(s"Don't know how to handle $newOut for $function")
      }
    }
  }*/
}
