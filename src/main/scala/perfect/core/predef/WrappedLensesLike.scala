package perfect.core.predef

import perfect.core._



trait WrappedLensesLike {
  self: ProgramUpdater with ContExps with Lenses with ADTLensesLike with StringLensesLike with LetLensesLike with ApplicationLensesLike with LambdaLensesLike with ListInsertLensesLike with StringConcatLensesLike with StringInsertLensesLike  =>

  class WrappedStringLensLike(StringLiteral: StringLiteralExtractor,
                              val StringConcat: StringConcatExtractor,
                              StringInsertLensGoal: StringInsertLensGoalExtractor,
                              Let: LetExtractor, Lambda: LambdaExtractor, Application: ApplicationExtractor)
      extends SemanticLens with StringConcatHelpers  {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      if (in.getFunctionValue.isEmpty) Stream.empty else {
        in.exp match {
          case Let(_, _, _) => Stream.empty[ContExp] // No need to wrap a let expression, we can always do this later. Indeed,
          //f{val x = A; B} = {val x = A; f(B)}
          case Application(Lambda(_, _, _), _) => Stream.empty[ContExp] // Same argument
          case _ if in.canDoStringWrapping  && freeVariables(in.exp).nonEmpty =>
            maybeWrapString(in, out) // #::: maybeUnwrapString(program, newOut, functionValue)
          case _ => Stream.empty
        }
      }
    }

    /* Example:
    inexp = f(a) + v + "boss"
    inexpValue = "I am the boss"
    out =  "Therefore, I am the boss"
    result: "Therefore, " + (f(a) + v + "boss")
    **/
    private def maybeWrapString(in: ContExp, out: ContExp)(implicit cache: Cache, symbols: Symbols): Stream[ContExp] = {
      val inexp = in.exp
      val inValue = in.getFunctionValue.getOrElse(return Stream.empty)
      if (inValue == out.exp) {
        return Stream(in.assignmentsAsOriginals())
      }
      val StringLiteral(t) = inValue

      def wrapToRight(s: String) = {
        val StringConcat.Exhaustive(atoms) = inexp
        if (atoms.lastOption.exists{ case StringLiteral(_) => true case _ => false} ) { // We don't wrap in a new string if the last concatenation is a StringLiteral
          Stream.empty
        } else {
          Stream(ContExp(StringConcat(inexp, StringLiteral(s))))
        }
      }

      def wrapToLeft(s: String) = {
        val StringConcat.Exhaustive(atoms) = inexp
        if (atoms.headOption.exists{ case StringLiteral(_) => true case _ => false}) { // We don't wrap in a new string if the last concatenation is a StringLiteral
          Stream.empty
        } else {
          Stream(ContExp(StringConcat(StringLiteral(s), inexp)))
        }
      }

      out.exp match {
        case StringLiteral(s) =>
          inexp match {
            case StringLiteral(_) => Stream.empty // We can always replace the StringLiteral later
            case _ => (if (s.startsWith(t)) wrapToRight(s.substring(t.length)) else Stream.empty) #:::
              (if (s.endsWith(t)) wrapToLeft(s.substring(0, s.length - t.length)) else Stream.empty)
          }
        case StringInsertLensGoal("", inserted, right, direction) if t == right => wrapToLeft(inserted)
        case StringInsertLensGoal(left, inserted, "", direction) if t == left => wrapToRight(inserted)
        case _ => Stream.empty
      }
    }
  }

  class WrappedADTLensLike(
                        ADT: ADTExtractor,
                        Let: LetExtractor,
                        Lambda: LambdaExtractor,
                        Application: ApplicationExtractor,
                        ListInsertLensGoal: ListInsertLensGoalExtractor) extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      if (in.getFunctionValue.isEmpty) Stream.empty else {
        in.exp match {
          case Let(_, _, _) => Stream.empty[ContExp] // No need to wrap a let expression, we can always do this later. Indeed,
          //f{val x = A; B} = {val x = A; f(B)}
          case Application(Lambda(_, _, _), _) => Stream.empty[ContExp] // Same argument
          case _ if freeVariables(in.exp).nonEmpty =>
            out.exp match {
              case l@ListInsertLensGoal(_, _, _, _, _) => Stream.empty
              case _ =>
                maybeWrap(in, out) #::: maybeUnwrap(in, out)
            }
          case _ => Stream.empty
        }
      }
    }
    isPreemptive = false

    /* Example:
    function = v
    functionValue = Element("b", List(), List(), List())
    out = Element("div", List(Element("b", List(), List(), List())), List(), List())
    result: Element("div", List(v), List(), List())
  * */
    private def maybeWrap(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      val inValue = in.getFunctionValue.getOrElse(return Stream.empty)
      val outValue = out.getFunctionValue.getOrElse(return Stream.empty)
      val function = in.exp
      if (inValue == outValue) return Stream.empty[ContExp] // Value returned in maybeUnwrap

      val containsFunctionValue = exists {
        case t if t == inValue => true
        case _ => false
      } _
      // Checks if the old value is inside the new value, in which case we add a wrapper.
      if (containsFunctionValue(outValue)) {
        val canWrap = outValue match {
          case ADT(args, argsBuilder) =>
            function match {
              case ADT(argsFun, _) =>
                if (!ADT.isSame(outValue, function)) {
                  true
                } else { // There might be a duplicate wrapping.
                  val argsWithIndex = args.zipWithIndex
                  val indexes = argsWithIndex.filter { case (arg, i) =>
                    containsFunctionValue(arg)
                  }
                  if (indexes.length >= 2) {
                    true
                  } else if (indexes.isEmpty) { // That's weird, should not happen.
                    //Log("##### Error: This cannot happen #####")
                    false
                  } else {
                    val (arg, i) = indexes.head
                    val shouldNotWrap = argsFun.zipWithIndex.forall { case (arg2, i2) =>
                      println(s"Testing if $arg2 is value: ${isValue(arg2)}")
                      i2 == i || isValue(arg2)
                    }
                    /*if(shouldNotWrap) {
                    println("~~~~~~~~~~ Did not wrap this ~~~~~~~~")
                    println("  " + function)
                    println(" =" + functionValue)
                    println("->" + newOut)
                    println(s"because we would have the same wrapping at index $i")
                  }*/
                    !shouldNotWrap
                  }
                }
              case _ => true
            }
          case _ => true
        }
        if (canWrap) {
          // We wrap the computation of functionValue with ADT construction
          val newFunction = postMap {
            case t if t == inValue => Some(function)
            case _ => None
          }(outValue)
          Stream(ContExp(newFunction))
        } else Stream.empty
      } else {
        Stream.empty
      }
    }


    /* Example:
  *  in:      Element("b", List(v, Element("span", List(), List(), List())), List(), List())
  *  inValue: Element("b", List(Element("span", List(), List(), List()), Element("span", List(), List(), List())), List(), List())
  *  out:     Element("span", List(), List(), List())
  *  result:  v  #::   Element("span", List(), List(), List()) #:: Stream.empty
  * */
    private def maybeUnwrap(in: ContExp, out: ContExp, _inValue: Option[Exp] = None)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      val outValue = out.getFunctionValue.getOrElse(return Stream.empty)
      val inValue = _inValue.getOrElse(in.getFunctionValue.getOrElse(return Stream.empty))
      if (inValue == outValue) {
        return Stream(in.assignmentsAsOriginals()) // Necessary because we just found the sub-program which corresponds to the output.
      }

      (in.exp, inValue) match {
        case (ADT(args, argsBuilder), ADT(argsValue, argsBuilder2)) =>
          // Checks if the old value is inside the new value, in which case we add a wrapper.
          argsValue.toStream.zipWithIndex.filter { case (arg, i) =>
            exists {
              case t if t == outValue => true
              case _ => false
            }(arg)
          }.flatMap { case (arg, i) =>
            maybeUnwrap(ContExp(args(i), in.context), out, Some(arg))
          }

        case _ => Stream.empty
      }
    }
  }
}