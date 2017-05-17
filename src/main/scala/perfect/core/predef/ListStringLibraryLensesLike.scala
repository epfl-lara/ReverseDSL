package perfect.core
package predef

import perfect.Log

/**
  * Created by Mikael on 16/05/2017.
  */
trait ListStringLibraryLensesLike { self: ProgramUpdater
    with ContExps with Lenses with ListLensesLike with ListInsertLensesLike
  with InvocationLensesLike with ApplicationLensesLike with StringLensesLike with StringInsertLensesLike =>

  class MkStringLensLike(ListLiteral: ListLiteralExtractor,
                         ListInsertLensGoal: ListInsertLensGoalExtractor,
                         Invocation: InvocationExtractor,
                         StringInsertLensGoal: StringInsertLensGoalExtractor,
                         StringLiteral: StringLiteralExtractor) extends InvocationLensLike(Invocation) {
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

    implicit class AugmentedList[A](l: List[A]) {
      def mapFirst(p: A => A): List[A] = l match {
        case Nil => Nil
        case head::tail => p(head)::tail
      }
      def mapLast(p: A => A): List[A] = l match {
        case Nil => Nil
        case init :+ last => init :+ p(last)
      }
    }

    def put(originalArgsValues: Seq[ContExp], out: ContExp, builder: Seq[Exp] => Exp)(implicit cache: Cache, symbols: Symbols): Stream[(Seq[ContExp], Cont)] = {
      val ContExp(originalInputExpr@ListLiteral(originalInput, listLiteralBuilder), originalInput_formula) = originalArgsValues.head
      val ContExp(infixExpr@StringLiteral(infix), _) = originalArgsValues.tail.head
      val originalInputList: List[String] = originalInput.map{
        case StringLiteral(l) => l
        case e => throw new Exception(s"not a string: $e")
      }
      out.exp match {
        case StringInsertLensGoal(left, inserted_, right, direction) =>
          var inserted = inserted_

          def middleInsertedPossible(inserted: String) = // All possible lists of inserted elements in the middle.
            (if (inserted != "" && infix.nonEmpty) {
              List(inserted.split(java.util.regex.Pattern.quote(infix)).toList)
            } else {
              Nil
            }) ++ List(List(inserted))

          // Priority to the insertion/modification/deletion of elements
          // If not ambiguous (e.g. infix selected and replaced, or infix empty), change the infix.
          sealed abstract class ElementOrInfix {
            def s: String
          }
          case class Element(s: String) extends ElementOrInfix
          case class Infix(s: String) extends ElementOrInfix

          implicit class AugmentedElementOrInfixList(l: List[ElementOrInfix]) {
            def toOriginalListExpr: List[Exp] = l.collect{ case e: Element => StringLiteral(e.s)}
          }

          val lElementOrInfix: List[ElementOrInfix] = originalInputList match {
            case Nil => Nil
            case head :: tail => (collection.mutable.ListBuffer[ElementOrInfix](Element(head)) /: tail) { case (l, e) => (l += Infix(infix)) += Element(e) }.toList
          }

          // If infix explicitly selected, we replace it.
          val all@(leftUntouched: List[ElementOrInfix],
          leftUpdated: String, // should be a prefix of notHandledList.map(_.s).mkString
          notHandledList: List[ElementOrInfix],
          rightUpdated: String, // should be a suffix of notHandledList.map(_.s).mkString
          rightUntouched: List[ElementOrInfix]) = {
            val Some(init) = lElementOrInfix.inits.find(l => left.startsWith(l.map(_.s).mkString))
            val remaining = lElementOrInfix.drop(init.length)
            val Some(tail) = remaining.tails.find(l => right.endsWith(l.map(_.s).mkString))
            (init, left.substring(init.map(_.s).mkString.length), remaining.take(remaining.length - tail.length),
              right.substring(0, right.length - tail.map(_.s).mkString.length), tail)
          }
          //Log("(lun,lup,nh,rup,run)="+all)

          //assert(notHandledList.map(_.s).mkString.startsWith(leftUpdated),
          //  "The repair given was inconsistent with previous function value")
          //assert(notHandledList.map(_.s).mkString.endsWith(rightUpdated),
          //  "The repair given was inconsistent with previous function value")

          val solutions = collection.mutable.ListBuffer[(Seq[ContExp], Cont)]()

          //     [leftUntouched   ][          notHandledList           ][rightUntouched]
          // ==> [leftUntouched   ]leftUpdated [inserted]rightUpdated   [rightUntouched]
          //When complete coverage, replace this if-then-else by this body because it's the same code with coverage

          if(notHandledList.length == 1 && notHandledList.head.isInstanceOf[Infix] ||
            notHandledList.isEmpty && infix == "" && direction == AssociativeInsert.InsertAutomatic &&
              leftUntouched.nonEmpty && rightUntouched.nonEmpty
          ) { // The prefix was selected and updated !
            solutions += ((Seq(ContExp(originalInputExpr, originalInput_formula.assignmentsAsOriginals),
              ContExp(StringInsertLensGoal(leftUpdated, inserted, rightUpdated, direction))), Cont()))
          } else if(notHandledList.length % 2 == 0) { // An insertion occurred either on the element before or the element after.
            // Some more elements have been possibly inserted as well. We prioritize splitting on the infix if it is not empty.
            (leftUntouched.lastOption, rightUntouched.headOption) match {
              case (someInfixOrNone, Some(firstElem: Element)) =>
                assert(someInfixOrNone.isEmpty || someInfixOrNone.get.isInstanceOf[Infix])
                inserted = leftUpdated + inserted + rightUpdated
                if(infix != "") { // TODO: Add weights to attach to lastElem or firstElem
                  if(inserted.endsWith(infix)) { // Only elements have been inserted.
                    solutions ++= (for{ lInserted <- middleInsertedPossible(inserted.substring(0, inserted.length - infix.length)) } yield
                      (Seq(ContExp(ListInsertLensGoal(
                        leftUntouched.toOriginalListExpr,
                        lInserted.map{ (s: String) => StringLiteral(s)},
                        rightUntouched.toOriginalListExpr)),
                        ContExp(infixExpr)), Cont())
                      )
                  } else { // Does not end with infix, hence there is an StringInsertion and maybe a ListInsert.
                    solutions ++= (for{ lInserted <- middleInsertedPossible(inserted)} yield {
                      val pf = ContExp(StringInsertLensGoal("", lInserted.last, firstElem.s, AssociativeInsert.InsertToRight))
                      if(lInserted.length == 1) {
                        val newExpr = listLiteralBuilder(
                          leftUntouched.toOriginalListExpr ++
                          List(pf.exp) ++
                          rightUntouched.tail.toOriginalListExpr)
                        (Seq(ContExp(newExpr, pf.context), ContExp(infixExpr)), Cont())
                      } else { // New elements have been furthermore inserted.
                        val newPf = ContExp(ListInsertLensGoal(
                          leftUntouched.toOriginalListExpr,
                          lInserted.init.map{ (s: String) => StringLiteral(s)},
                          (pf.exp :: rightUntouched.tail.toOriginalListExpr)), pf.context)
                        (Seq(newPf, ContExp(infixExpr)), Cont())
                      }
                    })
                  }
                } else { // Infix is empty.
                  assert(infix == "")
                  val infixModification = if(someInfixOrNone.isDefined)
                    List((Seq(ContExp(originalInputExpr, originalInput_formula.assignmentsAsOriginals), ContExp(StringInsertLensGoal("", inserted, "", direction))), Cont()))
                  else Nil

                  val elementToLeftModification = {  // Then the element to the left, if any
                    if(someInfixOrNone.isDefined) {
                      val ifAppend = ContExp(StringInsertLensGoal(leftUntouched.init.last.s, inserted, "", AssociativeInsert.InsertToLeft))
                      List((Seq(ContExp(
                        listLiteralBuilder(
                          leftUntouched.init.toOriginalListExpr ++
                          List(ifAppend.exp) ++
                          rightUntouched.toOriginalListExpr
                        ), ifAppend.context), ContExp(infixExpr)), Cont()))
                    } else Nil
                  }

                  val ifPrepend = ContExp(StringInsertLensGoal("", inserted, firstElem.s, direction))

                  val elementToRightModification = List(
                    // Then the element to the right.
                    (Seq(ContExp(
                      listLiteralBuilder(
                        leftUntouched.toOriginalListExpr ++
                        List(ifPrepend.exp) ++
                        rightUntouched.tail.toOriginalListExpr
                      ), ifPrepend.context), ContExp(infixExpr)), Cont()))

                  val toAdd = direction match {
                    case AssociativeInsert.InsertToLeft | AssociativeInsert.InsertAutomatic =>
                      infixModification ++ elementToLeftModification ++ elementToRightModification
                    case AssociativeInsert.InsertToRight =>
                      elementToRightModification ++ infixModification ++ elementToLeftModification
                  }

                  solutions ++= toAdd
                }

              case (Some(lastElem: Element), someInfixOrNone) =>
                assert(someInfixOrNone.isEmpty || someInfixOrNone.get.isInstanceOf[Infix])
                assert(infix != "" || someInfixOrNone.isEmpty) // Because else it would have been into left.
                inserted = leftUpdated + inserted + rightUpdated

                if(inserted.startsWith(infix) && infix != "") { // Only elements have been inserted.
                  solutions ++= (for{ lInserted <- middleInsertedPossible(inserted.substring(infix.length)) } yield
                    (Seq(ContExp(ListInsertLensGoal(
                      leftUntouched.toOriginalListExpr,
                      lInserted.map{ (s: String) => StringLiteral(s)},
                      rightUntouched.toOriginalListExpr)),
                      ContExp(infixExpr)), Cont())
                    )
                } else { // Does not start with infix, hence there is an StringInsertion and maybe a ListInsert.
                  solutions ++= (for{ lInserted <- middleInsertedPossible(inserted)} yield {
                    val pf = ContExp(StringInsertLensGoal(lastElem.s, lInserted.head, "", AssociativeInsert.InsertToLeft))
                    if(lInserted.length == 1) {
                      val newExpr = listLiteralBuilder(
                        leftUntouched.init.toOriginalListExpr ++
                        List(pf.exp) ++
                        rightUntouched.toOriginalListExpr)
                      (Seq(ContExp(newExpr, pf.context), ContExp(infixExpr)), Cont())
                    } else { // New elements have been furthermore inserted.
                      val newPf = ContExp(ListInsertLensGoal(
                        leftUntouched.init.toOriginalListExpr :+ pf.exp,
                        lInserted.tail.map{ (s: String) => StringLiteral(s)},
                        rightUntouched.toOriginalListExpr), pf.context)
                      (Seq(newPf, ContExp(infixExpr)), Cont())
                    }
                  })
                }

              case (None, None) => // Empty list since the beginning. We just add elements, splitting them if needed.
                solutions ++= (for { lInserted <- middleInsertedPossible(inserted) } yield {
                  (Seq(
                    ContExp(ListInsertLensGoal(
                      Nil,
                      lInserted.map(x => StringLiteral(x)),
                      Nil
                    )),
                    ContExp(infixExpr)
                  ), Cont())
                })
              case e => throw new Exception(s"[Internal error]: did not expect: $e")
            }
          } else { // notHandledList.length % 2 == 1
            (leftUntouched.lastOption, rightUntouched.headOption) match {
              case (Some(prev: Element), Some(next: Element)) =>
                assert(infix != "") // Else infix would have been taken in leftUntouched.
                inserted = leftUpdated + inserted + rightUpdated
                val (startsWithInfix, remainingInserted) = if(inserted.startsWith(infix)) (true, inserted.substring(infix.length)) else (false, inserted)
                val (endsWithInfix, finalInserted) = if(remainingInserted.endsWith(infix)) (true, remainingInserted.substring(0, remainingInserted.length - infix.length)) else (false, remainingInserted)

                solutions ++= (for{ lInserted <- middleInsertedPossible(finalInserted) } yield {
                  if(startsWithInfix && endsWithInfix) { // Pure insertion of the elements.
                    (Seq(ContExp(ListInsertLensGoal(
                      leftUntouched.toOriginalListExpr,
                      lInserted.map(x => StringLiteral(x)),
                      rightUntouched.toOriginalListExpr
                    )), ContExp(infixExpr)), Cont())
                  } else if(lInserted.length == 1) {
                    if(!startsWithInfix && !endsWithInfix) { // Merge of two elements by inserting something else.
                      // We report this as deleting the second argument and updating the first one with the value of the second.
                      // TODO: Do better once we have the technology of argument value rewriting.
                      val insertion = StringInsertLensGoal(prev.s, lInserted.head + next.s, "", AssociativeInsert.InsertAutomatic)
                      (Seq(ContExp(ListInsertLensGoal(
                        leftUntouched.init.toOriginalListExpr :+ insertion,
                        Nil,
                        rightUntouched.tail.toOriginalListExpr
                      )), ContExp(infixExpr)), Cont())
                    } else if(startsWithInfix && !endsWithInfix) { // We merge the insertion with the right element
                      val insertion = StringInsertLensGoal("", lInserted.last, next.s, AssociativeInsert.InsertToRight)
                      (Seq(ContExp(
                        listLiteralBuilder(
                          leftUntouched.toOriginalListExpr ++
                            (insertion +: rightUntouched.tail.toOriginalListExpr)
                        )), ContExp(infixExpr)), Cont())
                    } else /*if(!startsWithInfix && endsWithInfix) */{ // We merge the insertion with the right element
                      val insertion = StringInsertLensGoal(prev.s, lInserted.head, "", AssociativeInsert.InsertToLeft)
                      (Seq(ContExp(
                        listLiteralBuilder(
                          (leftUntouched.init.toOriginalListExpr :+ insertion) ++
                            rightUntouched.toOriginalListExpr
                        )), ContExp(infixExpr)), Cont())
                    }
                  } else { // lInserted.length > 1
                    if(!startsWithInfix && !endsWithInfix) { // There is room for modifying two elements and inserting the rest.
                      val insertionPrev = StringInsertLensGoal(prev.s, lInserted.head, "", AssociativeInsert.InsertToLeft)
                      val insertionNext = StringInsertLensGoal("", lInserted.last, next.s, AssociativeInsert.InsertToRight)
                      (Seq(ContExp(ListInsertLensGoal(
                        leftUntouched.init.toOriginalListExpr :+ insertionPrev,
                        lInserted.tail.init.map( x => StringLiteral(x) ),
                        insertionNext +: rightUntouched.tail.toOriginalListExpr
                      )), ContExp(infixExpr)), Cont())
                    } else if(startsWithInfix && !endsWithInfix) { // We merge the insertion with the right element
                      val insertion = StringInsertLensGoal("", lInserted.last, next.s, AssociativeInsert.InsertToRight)
                      (Seq(ContExp(ListInsertLensGoal(
                        leftUntouched.toOriginalListExpr,
                        lInserted.init.map(x => StringLiteral(x)),
                        (insertion +: rightUntouched.tail.toOriginalListExpr)
                      )), ContExp(infixExpr)), Cont())
                    } else /*if(!startsWithInfix && endsWithInfix)*/ { // We merge the insertion with the right element
                      val insertion = StringInsertLensGoal(prev.s, lInserted.head, "", AssociativeInsert.InsertToLeft)
                      (Seq(ContExp(ListInsertLensGoal(
                        leftUntouched.init.toOriginalListExpr :+ insertion,
                        lInserted.tail.map(x => StringLiteral(x)),
                        rightUntouched.toOriginalListExpr
                      )), ContExp(infixExpr)), Cont())
                    }
                  }
                })
              case (Some(_: Infix) | None, Some(_: Infix) | None) =>

                inserted = leftUpdated + inserted + rightUpdated
                // Simple insertion between two infixes.
                solutions ++= (for{ lInserted <- middleInsertedPossible(inserted) } yield {
                  (Seq(ContExp(ListInsertLensGoal(
                    leftUntouched.toOriginalListExpr,
                    lInserted.map(x => StringLiteral(x)),
                    rightUntouched.toOriginalListExpr
                  )), ContExp(infixExpr)), Cont())
                })
              case (Some(prev: Infix), Some(next: Element)) => throw new Exception("[Internal error]")
              case (Some(prev: Element), Some(next: Infix)) => throw new Exception("[Internal error]")
              case (None, Some(next: Element)) => // This would mean that notHandled is of even size, impossible
                throw new Exception("[Internal error]")
              case (Some(next: Element), None) => // This would mean that notHandled is of even size, impossible
                throw new Exception("[Internal error]")
            }
          }

          solutions.toStream

        case _ =>
          val newOut = out.getFunctionValue.flatMap(StringLiteral.unapply).getOrElse(return Stream.empty)
          val (before, middle, after) = separateModifs(originalInputList, infix, newOut)
          Log(s"Separator($originalInputList, '$infix', '$newOut')=")
          Log(s"($before, $middle, $after)")

          val notHandled = originalInputList.slice(before.length, originalInputList.length - after.length)
          val middleList: List[String] = if(infix.nonEmpty) { // We split middle using infix.
            middle.split(java.util.regex.Pattern.quote(infix)).toList
          } else { // We consider the new element as a new one.
            List(middle)
          }
          val list = listLiteralBuilder((before ++ middleList ++ after).map(x => StringLiteral(x)))
          Stream((Seq(ContExp(list), ContExp(StringLiteral(infix))), Cont()))
      }
    }
  }
}
