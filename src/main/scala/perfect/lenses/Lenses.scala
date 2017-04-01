package perfect
package lenses

import inox.Identifier
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import perfect.ImplicitTuples.{_1, _2, tuple2}

trait Lenses { self: ReverseProgram.type =>

  val reversers = List[Reverser](
    FilterReverser,
    MapReverser,
    ListConcatReverser,
    FlattenReverser,
    FlatMapReverser,
    StringConcatReverser,
    SplitEvenReverser,
    MergeReverser,
    SortWithReverser,
    MkStringReverser
  )

  val reversions = reversers.map(x => x.identifier -> x).toMap
  val funDefs = reversers.map(_.funDef) ++ List(
    mkFunDef(Utils.stringCompare)(){case _ =>
      (Seq("left"::StringType, "right"::StringType),
        Int32Type,
        { case Seq(l, r) =>
            StringLength(l) - StringLength(r) // Dummy
        })
    }
  )

  abstract class Reverser {
    def identifier: Identifier
    def funDef: FunDef
    def mapping = identifier -> this
    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: ProgramFormula)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ProgramFormula], Formula)]
  }

  object ListLiteral {
    import Utils._
    def unapply(e: Expr): Option[List[Expr]] = e match {
      case ADT(ADTType(cons, tps), Seq(head, tail)) =>
        unapply(tail).map(head :: _ )
      case ADT(ADTType(nil, tps), Seq()) =>
        Some(Nil)
      case _ => None
    }
    def apply(e: List[Expr], tps: Seq[Type]): Expr = e match {
      case head :: tail =>
        ADT(ADTType(cons, tps), Seq(head, apply(tail, tps)))
      case Nil =>
        ADT(ADTType(nil, tps), Seq())
    }
  }

  /** Lense-like filter */
  case object FilterReverser extends Reverser with FilterLike[Expr] { // TODO: Incorporate filterRev as part of the sources.
    import Utils._
    val identifier = Utils.filter
    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutputProgram: ProgramFormula)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ProgramFormula], Formula)] = {
      val lambda = originalArgsValues.tail.head
      val newOutput = newOutputProgram.expr
      val ListLiteral(originalInput) = originalArgsValues.head
      //Log(s"Reversing $originalArgs: $originalOutput => $newOutput")
      filterRev(originalInput, (expr: Expr) => evalWithCache(Application(lambda, Seq(expr))) == BooleanLiteral(true), ListLiteral.unapply(newOutput).get).map{ (e: List[Expr]) =>
        (Seq(ProgramFormula(ListLiteral(e, tpes)), ProgramFormula(lambda)), Formula())
      }
    }

    // filter definition in inox
    val funDef = mkFunDef(identifier)("A"){ case Seq(tp) =>
      (Seq("ls" :: T(list)(tp), "f" :: FunctionType(Seq(tp), BooleanType)),
        T(list)(tp),
        { case Seq(ls, f) =>
          if_(ls.isInstOf(T(cons)(tp))) {
            let("c"::T(cons)(tp), ls.asInstOf(T(cons)(tp)))(c =>
              let("head"::tp, c.getField(head))( head =>
                if_(Application(f, Seq(head))){
                  ADT(T(cons)(tp), Seq(head, E(identifier)(tp)(c.getField(tail), f)))
                } else_ {
                  E(identifier)(tp)(c.getField(tail), f)
                }
              )
            )
          } else_ {
            ADT(T(nil)(tp), Seq())
          }
        })
    }
  }

  /** Lense-like map, with the possibility of changing the mapping lambda. */
  case object MapReverser extends Reverser {
    import Utils._
    val identifier = map

    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: ProgramFormula)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ProgramFormula], Formula)] = {
      Log(s"map.apply($newOutput)")
      val lambda = castOrFail[Expr, Lambda](originalArgsValues.tail.head)
      val ListLiteral(originalInput) = originalArgsValues.head
      val uniqueUnknownValue = defaultValue(lambda.args.head.getType)
      // Maybe we change only arguments. If not possible, we will try to change the lambda.
      val mapr = new MapReverseLike[Expr, Expr, (Expr, Lambda)] {
        override def f = (expr: Expr) => evalWithCache(Application(lambda, Seq(expr)))

        override def fRev = (prevIn: Option[Expr], out: Expr) => {
          Log(s"Map.fRev: $prevIn, $out")
          val (Seq(in), newFormula) =
            prevIn.map(x => (Seq(x), Formula(Map[ValDef, Expr]()))).getOrElse {
              val unknown = ValDef(FreshIdentifier("unknown"),lambda.args.head.getType)
              (Seq(unknown.toVariable), Formula(Map[ValDef, Expr](unknown -> uniqueUnknownValue)))
            }
          Log(s"in:$in\nnewformula:$newFormula")
          Log.prefix("res=") :=
          repair(ProgramFormula(Application(lambda, Seq(in)), newFormula), newOutput.subExpr(out)).flatMap {
            case ProgramFormula(Application(_, Seq(in2)), _)
              if in2 != in => //The argument's values have changed
              Stream(Left(in2))
            case ProgramFormula(Application(_, Seq(in2)), f:Formula)
              if in2 == in && in2.isInstanceOf[Variable] =>
              // The repair introduced a variable. We evaluate all possible values.
              // TODO: Alternatively, propagate the constraint on the variable
              f.evalPossible(in2).map(Left(_))
            case e@ProgramFormula(Application(lambda2: Lambda, Seq(in2)), f:Formula)
              if in2 == in && lambda2 != lambda => // The lambda has changed.
              f.evalPossible(lambda2).map(lambda => Right((in, castOrFail[Expr, Lambda](lambda))))
            case e@ProgramFormula(app, f) =>
              throw new Exception(s"Don't know how to invert both the lambda and the value: $e")
          }.filter(_ != Left(uniqueUnknownValue))
        }
      }

      //Log(s"Reversing $originalArgs: $originalOutput => $newOutput")
      mapr.mapRev(originalInput, ListLiteral.unapply(newOutput.expr).get).flatMap(recombineArgumentsLambdas(lambda, tpes))
    }

    // Map definition in inox
    val funDef = mkFunDef(identifier)("A", "B"){ case Seq(tA, tB) =>
      (Seq("ls" :: T(list)(tA), "f" :: FunctionType(Seq(tA), tB)),
        T(list)(tB),
        { case Seq(ls, f) =>
          if_(ls.isInstOf(T(cons)(tA))) {
            let("c"::T(cons)(tA), ls.asInstOf(T(cons)(tA)))(c =>
              let("head"::tA, c.getField(head))( head =>
                ADT(T(cons)(tB), Seq(Application(f, Seq(head)), E(identifier)(tA, tB)(c.getField(tail), f)))
              )
            )
          } else_ {
            ADT(T(nil)(tB), Seq())
          }
        })
    }
  }

  /** Lense-like map, with the possibility of changing the mapping lambda. */
  case object FlattenReverser extends Reverser {
    import Utils._
    val identifier = flatten

    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutputProgram: ProgramFormula)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ProgramFormula], Formula)] = {
???
    }

    // Flatten definition in inox
    val funDef = mkFunDef(identifier)("A"){ case Seq(tA) =>
      (Seq("ls" :: T(list)(T(list)(tA))),
        T(list)(tA),
        { case Seq(ls) =>
          if_(ls.isInstOf(T(cons)(T(list)(tA)))) {
            let("c"::T(cons)(T(list)(tA)), ls.asInstOf(T(cons)(T(list)(tA))))(c =>
              let("head"::T(list)(tA), c.getField(head))( head =>
                FunctionInvocation(listconcat, Seq(tA), Seq(head,
                  FunctionInvocation(identifier, Seq(tA), Seq(c.getField(tail)))
                ))
              )
            )
          } else_ {
            ADT(T(nil)(T(list)(tA)), Seq())
          }
        })
    }
  }

  case object MkStringReverser extends Reverser {
    import Utils._
    import StringConcatExtended._
    val identifier = mkString

    private def separateModifs(in: List[String], infix: String, out: String): (List[String], String, List[String]) = {
      in match {
        case Nil => (Nil, out, Nil)
        case lOutHead::tail =>
          if(out.startsWith(lOutHead + infix)) {
            val (before, middle, after) = separateModifs(in.tail, infix, out.drop(lOutHead.length + infix.length))
            (lOutHead :: before, middle, after)
          } else if(out == lOutHead) { // Last element
            (lOutHead::Nil, "", Nil)
          } else {
            val optI = (0 to in.length).find { i =>
              out.endsWith(in.drop(i).map(infix + _).mkString)
            }
            assert(optI.isInstanceOf[Some[Int]], "[Internal error] should not happen")
            val i = optI.asInstanceOf[Some[Int]].get
            val after = in.drop(i)
            (Nil, out.take(out.length - after.map(infix + _).mkString.length), after)
          }
      }
    }

    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutputProgram: ProgramFormula)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ProgramFormula], Formula)] = {
      val ListLiteral(originalInput) = originalArgsValues.head
      val StringLiteral(infix) = originalArgsValues.tail.head
      val originalInputList: List[String] = originalInput.map{
        case StringLiteral(l) => l
        case e => throw new Exception(s"not a string: $e")
      }
      newOutputProgram match {
//        case ProgramFormula.StringInsert(left, inserted, right) =>

        case _ =>
          val StringLiteral(newOut) = newOutputProgram.functionValue
          val (before, middle, after) = separateModifs(originalInputList, infix, newOut)
          Log(s"Separator($originalInputList, '$infix', '$newOut')=")
          Log(s"($before, $middle, $after)")

          val notHandled = originalInputList.drop(before.length).take(originalInputList.length - before.length - after.length)
          val middleList: List[String] = if(infix.nonEmpty) { // We split middle using infix.
            middle.split(java.util.regex.Pattern.quote(infix)).toList
          } else { // We consider the new element as a new one.
            List(middle)
          }
          val list = ListLiteral((before ++ middleList ++ after).map(x => StringLiteral(x)), Seq(StringType))
          Stream((Seq(ProgramFormula(list), ProgramFormula(StringLiteral(infix))), Formula()))
      }
    }

    // Flatten definition in inox
    val funDef = mkFunDef(identifier)(){ case Seq() =>
      (Seq("ls" :: T(list)(StringType), "infix"::StringType),
        StringType,
        { case Seq(ls, infix) =>
          if_(ls.isInstOf(T(cons)(StringType))) {
            let("c"::T(cons)(StringType), ls.asInstOf(T(cons)(StringType)))(c =>
              let("head"::StringType, c.getField(head))( head =>
                let("tail"::T(list)(StringType), c.getField(tail))( tail =>
                  if_(tail.isInstOf(T(cons)(StringType))) {
                    head +& infix +& FunctionInvocation(identifier, Seq(), Seq(tail, infix))
                  } else_ {
                    head
                  }
              )
            )
            )
          } else_ {
            StringLiteral("")
          }
        })
    }
  }

  private def recombineArgumentsLambdas(lambda: Lambda, tpes: Seq[Type])(e: List[Either[Expr, (Expr, Lambda)]]) = {
    val argumentsChanged = e.map{
      case Left(e) => e
      case Right((e, lambda)) => e
    }
    val newLambdas = if(e.exists(_.isInstanceOf[Right[_, _]])) {
      e.collect{ case Right((expr, lambda: Lambda)) => lambda }.toStream
    } else Stream(lambda)
    for(l <- newLambdas) yield {
      (Seq(ProgramFormula(ListLiteral(argumentsChanged, tpes.take(1))), ProgramFormula(l)), Formula())
    }
  }

  /** Lense-like map, with the possibility of changing the mapping lambda. */
  case object FlatMapReverser extends Reverser {
    import Utils._
    val identifier = flatmap

    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: ProgramFormula)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ProgramFormula], Formula)] = {
      val ListLiteral(originalInput) = originalArgsValues.head
      val lambda = castOrFail[Expr, Lambda](originalArgsValues.tail.head)
      val uniqueUnknownValue = defaultValue(lambda.args.head.getType)

      val fmapr = new FlatMapReverseLike[Expr, Expr, (Expr, Lambda)] {
        def f: Expr => List[Expr] = { (expr: Expr) =>
          val ListLiteral(l) = evalWithCache(Application(lambda, Seq(expr)))
          l
        }
        def fRev: (Option[Expr], List[Expr]) => Stream[Either[Expr, (Expr, Lambda)]] = { (prevIn, out) =>
          Log(s"Flatmap.fRev: $prevIn, $out")
          val (Seq(in), newFormula) =
            prevIn.map(x => (Seq(x), Formula(Map[ValDef, Expr]()))).getOrElse {
              val unknown = ValDef(FreshIdentifier("unknown"),lambda.args.head.getType)
              (Seq(unknown.toVariable), Formula(Map[ValDef, Expr](unknown -> uniqueUnknownValue)))
            }
          Log(s"flatmap in:$in\nnewformula:$newFormula")
          Log.res :=
            repair(ProgramFormula(Application(lambda, Seq(in)), newFormula), newOutput.subExpr(ListLiteral(out, tpes.drop(1)))).flatMap {
              case ProgramFormula(Application(_, Seq(in2)), _)
                if in2 != in => //The argument's values have changed
                Stream(Left(in2))
              case ProgramFormula(Application(_, Seq(in2)), f:Formula)
                if in2 == in && in2.isInstanceOf[Variable] =>
                // The repair introduced a variable. We evaluate all possible values.
                // TODO: Alternatively, propagate the constraint on the variable
                f.evalPossible(in2).map(Left(_))
              case e@ProgramFormula(Application(lambda2: Lambda, Seq(in2)), f:Formula)
                if in2 == in && lambda2 != lambda => // The lambda has changed.
                f.evalPossible(lambda2).map(lambda => Right((in, castOrFail[Expr, Lambda](lambda))))
              case e@ProgramFormula(app, f) =>
                throw new Exception(s"Don't know how to invert both the lambda and the value: $e")
            }.filter(_ != Left(uniqueUnknownValue))
        }
      }

      fmapr.flatMapRev(originalInput, ListLiteral.unapply(newOutput.expr).get).flatMap(recombineArgumentsLambdas(lambda, tpes))
    }

    // Flatmap definition in inox
    val funDef = mkFunDef(identifier)("A", "B"){ case Seq(tA, tB) =>
      (Seq("ls" :: T(list)(tA), "f" :: FunctionType(Seq(tA), T(list)(tB))),
        T(list)(tB),
        { case Seq(ls, f) =>
          if_(ls.isInstOf(T(cons)(tA))) {
            let("c"::T(cons)(tA), ls.asInstOf(T(cons)(tA)))(c =>
              let("headMapped"::T(list)(tB), f(c.getField(head)))( headMapped =>
                E(listconcat)(tB)(headMapped, E(identifier)(tA, tB)(c.getField(tail), f))
              )
            )
          } else_ {
            ADT(T(nil)(tB), Seq())
          }
        })
    }
  }


  /** Lense-like list concat, with the possibility of changing the mapping lambda. */
  case object ListConcatReverser extends Reverser {
    import Utils._
    val identifier = listconcat

    def startsWith(list: Expr, beginning: Expr): Boolean = (list, beginning) match {
      case (ADT(_, Seq(head, tail)), ADT(_, Seq())) => true
      case (ADT(_, Seq(head, tail)), ADT(_, Seq(head2, tail2))) =>
        head == head2 && startsWith(tail, tail2)
      case _ => false
    }

    def reverse(list: Expr, gather: Option[Expr]): Expr = list match {
      case ADT(tpe@ADTType(c, targs), Seq(head, tail)) =>
        val gathertail = gather.getOrElse(ADT(ADTType(nil, targs), Seq()))
        reverse(tail, Some(ADT(tpe, Seq(head, gathertail))))
      case ADT(_, Seq()) => gather.getOrElse(list)
    }

    def endsWith(list: Expr, end: Expr): Boolean = startsWith(reverse(list, None), reverse(end, None))

    def put(tps: Seq[Type])(originalArgsValues: Seq[Expr], newOutputProgram: ProgramFormula)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ProgramFormula], Formula)] = {
      val newOutput = newOutputProgram.expr
      val leftValue = originalArgsValues.head
      val rightValue = originalArgsValues.tail.head

      def defaultCase: Stream[(Seq[ProgramFormula], Formula)] = {
        val left = ValDef(FreshIdentifier("l", true), T(list)(tps.head), Set())
        val right = ValDef(FreshIdentifier("r", true), T(list)(tps.head), Set())
        Log(s"List default case: ${left.id} + ${right.id} == $newOutput")

        val f = Formula(
          newOutput === FunctionInvocation(listconcat, tps, Seq(left.toVariable, right.toVariable)) &&
          not(left.toVariable === leftValue) && not(right.toVariable === rightValue)
        )

        Stream((Seq(ProgramFormula(left.toVariable), ProgramFormula(right.toVariable)), f))
      }

      // Prioritize changes that touch only one of the two expressions.
      newOutput match {
        case ListLiteral(s) =>
          (leftValue match {
            case ListLiteral(lv) =>
              if (s.startsWith(lv)) {
                Stream((Seq(ProgramFormula(leftValue), ProgramFormula(ListLiteral(s.drop(lv.length), tps))), Formula()))
              } else Stream.empty
            case _ => Stream.empty
          }) #::: (
            rightValue match {
              case ListLiteral(rv) =>
                if (s.endsWith(rv)) {
                  Stream((Seq(ProgramFormula(ListLiteral(s.take(s.length - rv.length), tps)), ProgramFormula(rightValue)), Formula()))
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
      (Seq("left" :: T(list)(tA), "right" :: T(list)(tA)),
        T(list)(tA),
        { case Seq(left, right) =>
          if_(left.isInstOf(T(cons)(tA))) {
            let("c"::T(cons)(tA), left.asInstOf(T(cons)(tA)))(c =>
              ADT(T(cons)(tA),
                Seq(c.getField(head), E(identifier)(tA)(c.getField(tail), right)))
            )
          } else_ {
            right
          }
        })
    }
  }

  /** Lense-like list concat, with the possibility of changing the mapping lambda. */
  case object StringConcatReverser extends Reverser {
    import StringConcatExtended._
    import Utils._
    val identifier = FreshIdentifier("tmpstringconcat")

    def put(tps: Seq[Type])(originalArgsValues: Seq[Expr], newOutputProgram: ProgramFormula)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ProgramFormula], Formula)] = {
      val newOutput = newOutputProgram.expr
      val leftValue = originalArgsValues.head
      val rightValue = originalArgsValues.tail.head

      def leftCase(s: String):  Stream[(Seq[ProgramFormula], Formula)] = {
        Log.prefix("Testing left:") := (leftValue match {
          case StringLiteral(lv) =>
            (if (s.startsWith(lv)) {
              Stream((Seq(ProgramFormula(leftValue), ProgramFormula(StringLiteral(s.drop(lv.length)))), Formula()))
            } else Stream.empty)  /:: Log.prefix("left worked:")
          case _ => Stream.empty
        })
      }

      def rightCase(s: String): Stream[(Seq[ProgramFormula], Formula)] = {
        Log.prefix("Testing right:") := (rightValue match {
          case StringLiteral(rv) =>
            (if (s.endsWith(rv)) {
              Stream((Seq(ProgramFormula(StringLiteral(s.take(s.length - rv.length))), ProgramFormula(rightValue)), Formula()))
            } else Stream.empty)  /:: Log.prefix("right worked:")
          case _ => Stream.empty
        })
      }

      def defaultCase(addMaybes: Boolean = false): Stream[(Seq[ProgramFormula], Formula)] = {
        val left = ValDef(FreshIdentifier("l", true), StringType, Set())
        val right = ValDef(FreshIdentifier("r", true), StringType, Set())
        Log(s"String default case: ${left.id} + ${right.id} == $newOutput:")

        val newConstraint = (newOutput === FunctionInvocation(identifier, tps, Seq(left.toVariable, right.toVariable))
        &<>& (if(addMaybes)
          E(maybe)(left.toVariable === leftValue) && E(maybe)(right.toVariable === rightValue)
        else BooleanLiteral(true)
        ) // Maybe use what is below for faster convergence?
        //            (if(addMaybes) not(left.toVariable === leftValue) && not(right.toVariable === rightValue)
          )
        val newVarsInConstraint = exprOps.variablesOf(newConstraint).map(_.toVal)
        val f = Formula(unknownConstraints = newConstraint)

        Stream((Seq(ProgramFormula(left.toVariable), ProgramFormula(right.toVariable)), f))
      }

      // Prioritize changes that touch only one of the two expressions.
      newOutputProgram match {
        case ProgramFormula.StringInsert(leftAfter, inserted, rightAfter) =>
          val StringLiteral(rightValue_s) = rightValue
          val StringLiteral(leftValue_s) = leftValue
          val totalValue_s = leftValue_s + rightValue_s
          // Put in first the one to which we removed the most chars.

          // leftValue + rightValue ==> leftAfter + inserted + rightAfter
          val res: List[((Seq[ProgramFormula], Formula), (Int, Int))] = (rightValue_s.endsWith(rightAfter)).flatMap{ // the insertion may have happened on the right.
            //  [  leftValue    ...     ][rightValue_s  ]
            //  [ leftAfter ....            ][rightAfter]

            // rightValue => (leftAfter \ leftValue) + inserted + rightAfter
            val newLeftAfter = if(leftValue_s.length < leftAfter.length) leftAfter.substring(leftValue_s.length) else ""
            val newRightAfter = rightAfter

            val newInsert = ProgramFormula.StringInsert(
              StringLiteral(newLeftAfter),
              StringLiteral(inserted),
              StringLiteral(newRightAfter))
            val newLeftValue = if(leftValue_s.length <= leftAfter.length) { // Nothing deleted.
              leftValue
            } else {
              StringLiteral(leftValue_s.substring(0, leftAfter.length))
            }
            val spaceWeight = (
                Distances.spaceJump(newLeftAfter, inserted).flatMap(List(1)) ++
                Distances.spaceJump(inserted, newRightAfter).flatMap(List(1))
              ).length
            val overwriteWeight = rightAfter.length - rightValue_s.length

            List((((Seq(ProgramFormula(newLeftValue), newInsert)), Formula()), (spaceWeight, overwriteWeight))) /: Log.Right_insert
          } ++
          (leftValue_s.startsWith(leftAfter)).flatMap{ // the insertion happened on the left.
            //  [  leftValue    ...     ][rightValue_s  ]
            //  [ leftAfter ...   ][        rightAfter  ]

            // leftValue => leftAfter + inserted + (rightAfter \ rightValue)

            val newLeftAfter = leftAfter
            val newRightAfter = if(rightValue_s.length < rightAfter.length) rightAfter.substring(0, rightAfter.length - rightValue_s.length) else ""

            val newInsert = ProgramFormula.StringInsert(
              StringLiteral(newLeftAfter),
              StringLiteral(inserted),
              StringLiteral(newRightAfter))

            val newRightValue = if(rightValue_s.length <= rightAfter.length) {
              rightValue
            } else {
              StringLiteral(rightValue_s.substring(rightValue_s.length - rightAfter.length))
            }
            val spaceWeight = (
                Distances.spaceJump(newLeftAfter, inserted).flatMap(List(1)) ++
                Distances.spaceJump(inserted, newRightAfter).flatMap(List(1))
              ).length
            val overwriteWeight = leftAfter.length - leftValue_s.length

            List(((Seq(newInsert, ProgramFormula(newRightValue)), Formula()), (spaceWeight, overwriteWeight))) /: Log.Left_insert
          }

          res.sortWith{ (x, y) => x._2._1 < y._2._1 || (x._2._1 == y._2._1 && x._2._2 < y._2._2)}.map(_._1).toStream

        case ProgramFormula.StringDelete(leftAfter, rightAfter) =>
          val StringLiteral(rightValue_s) = rightValue
          val StringLiteral(leftValue_s) = leftValue
          // leftValue + rightValue ==> leftAfter + rightAfter
          Stream((Seq(
            if(leftValue_s.length > leftAfter.length) {
              ProgramFormula.StringDelete(
                StringLiteral(leftAfter),
                StringLiteral(if(rightValue_s.length < rightAfter.length) rightAfter.substring(0, rightAfter.length - rightValue_s.length) else "")
              ) /: Log.Left_delete
            } else ProgramFormula(leftValue)
            ,
            if(rightValue_s.length > rightAfter.length) {
              ProgramFormula.StringDelete(
                StringLiteral(if(leftValue_s.length < leftAfter.length) leftAfter.substring(leftValue_s.length) else ""),
                StringLiteral(rightAfter)
              ) /: Log.Right_delete
            } else ProgramFormula(rightValue)
          ), Formula()))
        case ProgramFormula(StringLiteral(s), _) =>
          rightCase(s) append leftCase(s) append {
            defaultCase(false)
          }
        case ProgramFormula(StringConcat(StringLiteral(left), right), _) => // TODO !!
          val leftValue_s = asStr(leftValue)
          if(leftValue_s.startsWith(left)) {
            val newLeftValue = leftValue_s.substring(left.length)
            put(tps)(Seq(StringLiteral(newLeftValue), rightValue), newOutputProgram.subExpr(right))
          } else {
            ???
          }
        case ProgramFormula(StringConcat(left, StringLiteral(right)), _) => // TODO !!
          //leftValue = "Hello big " && rightValue == "beautiful world" && right = " world"
          val rightValue_s = asStr(rightValue)
          if(rightValue_s.endsWith(right)) {
            val newRightValue = rightValue_s.substring(0, rightValue_s.length - right.length)
            put(tps)(Seq(leftValue, StringLiteral(newRightValue)), newOutputProgram.subExpr(left))
          } else {
            ???
          }
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

  case object SplitEvenReverser extends Reverser {
    import Utils._
    import ImplicitTuples._
    val identifier = splitEven
    val funDef: FunDef = mkFunDef(identifier)("A") { case Seq(tA) =>
      (Seq("l"::T(list)(tA)),
       T(tuple2)(T(list)(tA), T(list)(tA)),
        { case Seq(l) =>
          if_(l.isInstOf(T(cons)(tA))) {
            let("r"::T(tuple2)(T(list)(tA), T(list)(tA)),
              FunctionInvocation(identifier, Seq(tA), Seq(l.asInstOf(T(cons)(tA)).getField(tail))))(r =>
              ADT(T(tuple2)(T(list)(tA), T(list)(tA)), Seq(
                ADT(T(cons)(tA), Seq(l.asInstOf(T(cons)(tA)).getField(head), r.getField(_2))),
                r.getField(_1))))
          } else_ {
            ADT(T(tuple2)(T(list)(tA), T(list)(tA)), Seq(ADT(T(nil)(tA), Seq()), ADT(T(nil)(tA), Seq())))
          }
        }
      )
    }
    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: ProgramFormula)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ProgramFormula], Formula)] = {
      ???
    }
  }

  // Merge two sorted lists.
  case object MergeReverser extends Reverser {
    import Utils._
    val identifier = merge
    val funDef : FunDef = mkFunDef(identifier)("A") { case Seq(tA) =>
      (Seq("left":: T(list)(tA), "right":: T(list)(tA), "comp" :: FunctionType(Seq(tA, tA), Int32Type)),
        T(list)(tA),
        { case Seq(left, right, comp) =>
          if_(left.isInstOf(T(cons)(tA))) {
            if_(right.isInstOf(T(cons)(tA))) {
              let("leftcons"::T(cons)(tA), left.asInstOf(T(cons)(tA)))( leftcons =>
                let("rightcons"::T(cons)(tA), right.asInstOf(T(cons)(tA)))( rightcons =>
                  if_(Application(comp, Seq(leftcons.getField(head), rightcons.getField(head))) <= IntLiteral(0)) {
                    ADT(T(cons)(tA), Seq(leftcons.getField(head), FunctionInvocation(identifier, Seq(tA), Seq(leftcons.getField(tail), right, comp))))
                  } else_ {
                    ADT(T(cons)(tA), Seq(rightcons.getField(head), FunctionInvocation(identifier, Seq(tA), Seq(left, rightcons.getField(tail), comp))))
                  }
                )
              )
            } else_ {
              left
            }
          } else_ {
            right
          }
        })
    }
    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr],
                             newOutput: ProgramFormula)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ProgramFormula], Formula)] = {
      ???
    }
  }

  case object SortWithReverser extends Reverser {
    import Utils._
    val identifier = sortWith
    import InoxConvertible._

    val funDef: inox.trees.FunDef = mkFunDef(identifier)("A"){ case Seq(tA) =>
      (Seq("in" :: T(list)(tA), "comp" :: FunctionType(Seq(tA, tA), Int32Type)),
      T(list)(tA),
      { case Seq(input, comp) =>
          if_(input.isInstOf(T(nil)(tA)) || input.asInstOf(T(cons)(tA)).getField(tail).isInstOf(T(nil)(tA))) {
            input
          } else_ {
            let("r"::T(tuple2)(T(list)(tA), T(list)(tA)),
              FunctionInvocation(splitEven, Seq(tA), Seq(input)))( r=>
              FunctionInvocation(merge, Seq(tA), Seq(
                FunctionInvocation(sortWith, Seq(tA), Seq(r.getField(_1), comp)),
                FunctionInvocation(sortWith, Seq(tA), Seq(r.getField(_2), comp)),
                comp))
            )
          }
      })
    }

    def put(tpes: Seq[Type])(originalArgsValues: Seq[Expr], newOutput: ProgramFormula)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ProgramFormula], Formula)] = {
      ???
    }
  }
}
