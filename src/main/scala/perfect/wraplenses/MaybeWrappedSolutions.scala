package perfect
package wraplenses

import inox._
import inox.trees._
import inox.trees.dsl._

import semanticlenses._
import ReverseProgram.Cache
import Utils.isValue

/**
  * Created by Mikael on 05/05/2017.
  */
object MaybeWrappedSolutions extends SemanticLens {
  def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    if (in.getFunctionValue.isEmpty) Stream.empty else (in.expr.getType match {
      case a: ADTType if !out.expr.isInstanceOf[Variable] && exprOps.variablesOf(in.expr).nonEmpty =>
        in.expr match {
          case l: Let => Stream.empty[ProgramFormula] // No need to wrap a let expression, we can always do this later. Indeed,
          //f{val x = A; B} = {val x = A; f(B)}
          case Application(Lambda(_, _), _) => Stream.empty[ProgramFormula] // Same argument
          case _ if ListInsert.unapply(out).nonEmpty => Stream.empty[ProgramFormula]
          case _ =>
            (maybeWrap(in, out, in.getFunctionValue.get) /:: Log.maybe_wrap) #::: (maybeUnwrap(in, out, in.getFunctionValue.get) /:: Log.maybe_unwrap)
        }
      case StringType if !out.expr.isInstanceOf[Variable] && in.canDoWrapping =>
        in.expr match {
          case l: Let => Stream.empty[ProgramFormula]
          case Application(Lambda(_, _), _) => Stream.empty[ProgramFormula]
          case _ =>
            // Stream.empty
            // Can be a StringConcat with constants to add or to remove.
            maybeWrapString(in, out.expr, in.getFunctionValue.get) // #::: maybeUnwrapString(program, newOut, functionValue)
        }
      case _ => Stream.empty[ProgramFormula]
    })
  }
  isPreemptive = false

  /* Example:
    function = v
    functionValue = Element("b", List(), List(), List())
    newOut = Element("div", List(Element("b", List(), List(), List())), List(), List())
    result: Element("div", List(v), List(), List())
  * */
  private def maybeWrap(program: ProgramFormula, newOutProgram: ProgramFormula, functionValue: Expr)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    //Log(s"Testing maybewrap for function Value = $functionValue")
    val newOut = newOutProgram.getFunctionValue.getOrElse(return Stream.empty)
    val function = program.expr
    if(functionValue == newOut) return Stream.empty[ProgramFormula] // Value returned in maybeUnwrap
    //Log(s"maybewrap 2")

    val containsFunctionValue = exprOps.exists {
      case t if t == functionValue => true
      case _ => false
    } _
    // Checks if the old value is inside the new value, in which case we add a wrapper.
    if (containsFunctionValue(newOut)) {
      Log(s"maybewrap 3")
      val canWrap = newOut match {
        case ADT(ADTType(name, tps), args) =>
          function match {
            case ADT(ADTType(nameFun, tpsFun), argsFun) =>
              if(name != nameFun || tps != tpsFun) {
                true
              } else { // There might be a duplicate wrapping.
                val argsWithIndex = args.zipWithIndex
                val indexes = argsWithIndex.filter{ case (arg, i) =>
                  containsFunctionValue(arg)
                }
                if(indexes.length >= 2) {
                  true
                } else if(indexes.isEmpty) { // That's weird, should not happen.
                  Log("##### Error: This cannot happen #####")
                  false
                } else {
                  val (arg, i) = indexes.head
                  val shouldNotWrap = argsFun.zipWithIndex.forall{ case (arg2, i2) =>
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
      Log(s"canwrap: $canWrap")
      if(canWrap) {
        // We wrap the computation of functionValue with ADT construction
        val newFunction = exprOps.postMap {
          case t if t == functionValue => Some(function)
          case _ => None
        }(newOut)
        Stream(ProgramFormula(newFunction))
      } else Stream.empty
    } else {
      Stream.empty
    }
  }


  /* Example:
  *  function:      Element("b", List(v, Element("span", List(), List(), List())), List(), List())
  *  functionValue: Element("b", List(Element("span", List(), List(), List()), Element("span", List(), List(), List())), List(), List())
  *  newOut:        Element("span", List(), List(), List())
  *  result:        v  #::   Element("span", List(), List(), List()) #:: Stream.empty
  * */
  private def maybeUnwrap(program: ProgramFormula, newOutProgram: ProgramFormula, functionValue: Expr)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    //Log(s"Testing maybeUnwrap for function Value = $functionValue")
    val newOut = newOutProgram.getFunctionValue.getOrElse(return Stream.empty)
    val function = program.expr
    if(functionValue == newOut) {
      Log("@return unwrapped")
      return Stream(program.assignmentsAsOriginals()) // Necessary because we just found the sub-program which corresponds to the output.
    }

    (function, functionValue) match {
      case (ADT(ADTType(tp, tpArgs), args), ADT(ADTType(tp2, tpArgs2), argsValue)) =>
        // Checks if the old value is inside the new value, in which case we add a wrapper.
        argsValue.toStream.zipWithIndex.filter{ case (arg, i) =>
          exprOps.exists {
            case t if t == newOut => true
            case _ => false
          }(arg)
        }.flatMap{ case (arg, i) =>
          maybeUnwrap(ProgramFormula(args(i), program.formula), newOutProgram, arg)
        }

      case _ => Stream.empty
    }
  }

  /* Example:
    function = f(a) + v + "boss"
    functionValue = "I am the boss"
    newOut =  "Therefore, I am the boss"
    result: "Therefore, " + (f(a) + v + "boss")
  * */
  private def maybeWrapString(program: ProgramFormula, newOut: Expr, functionValue: Expr)(implicit symbols: Symbols): Stream[ProgramFormula] = {
    val function = program.expr
    if(functionValue == newOut) {
      Log("@return unwrapped")
      return Stream(program.assignmentsAsOriginals())
    }
    val StringLiteral(t) = functionValue

    object StringConcats {
      def unapply(e: Expr): Some[List[Expr]] = e match {
        case StringConcat(a, b) => Some(unapply(a).get ++ unapply(b).get)
        case e => Some(List(e))
      }
    }

    def wrapToRight(s: String) = {
      val StringConcats(atoms) = function
      if(atoms.lastOption.exists(x => x.isInstanceOf[StringLiteral])) { // We don't wrap in a new string if the last concatenation is a StringLiteral
        Stream.empty
      } else {
        Stream(ProgramFormula(StringConcat(function, StringLiteral(s))))
      }
    }

    def wrapToLeft(s: String) = {
      val StringConcats(atoms) = function
      if(atoms.headOption.exists(x => x.isInstanceOf[StringLiteral])) { // We don't wrap in a new string if the last concatenation is a StringLiteral
        Stream.empty
      } else {
        Stream(ProgramFormula(StringConcat(StringLiteral(s), function)))
      }
    }

    newOut match {
      case StringLiteral(s) =>
        function match {
          case StringLiteral(_) => Stream.empty // We can always replace the StringLiteral later
          case _ => (
            (if(s.startsWith(t)) wrapToRight(s.substring(t.length)) else Stream.empty) #:::
              (if(s.endsWith(t)) wrapToLeft(s.substring(0, s.length - t.length)) else Stream.empty)
            ) /:: Log.prefix("@return wrapped: ")
        }
      case StringInsert.Goal("", inserted, right, direction) if t == right => wrapToLeft(inserted)
      case StringInsert.Goal(left, inserted, "", direction) if t == left => wrapToRight(inserted)
      case _ => Stream.empty
    }
  }
}