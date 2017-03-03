import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import inox.InoxProgram

import scala.reflect.ClassTag

/**
  * Created by Mikael on 03/03/2017.
  */
object ReverseProgram {
  type FunctionEntry = Identifier
  type ModificationSteps = Unit
  type OutExpr = Expr
  import Utils._
  import Constrainable._
  lazy val context = Context.empty.copy(options = Options(Seq(optSelectedSolvers(Set("smt-cvc4")))))

  /** Reverses a parameterless function, if possible.*/
  def put[A: Constrainable](out: A, prevOut: Option[OutExpr], modif: Option[ModificationSteps], prevIn: Option[(InoxProgram, FunctionEntry)]): Iterable[(InoxProgram, FunctionEntry)] = {
    val outExpr = inoxExprOf[A](out)
    implicit val symbols = defaultSymbols
    if(prevIn == None) {
      val main = FreshIdentifier("main")
      val fundef = mkFunDef(main)()(stp => (Seq(), outExpr.getType, _ => outExpr))
      return Stream((InoxProgram(context, Seq(fundef), allConstructors), main))
    }
    val (prevProgram, prevFunctionEntry) = prevIn.get
    val prevFunction = prevProgram.symbols.functions.getOrElse(prevFunctionEntry, return Nil)
    val prevBody = prevFunction.fullBody
    val newMain = FreshIdentifier("main")
    for {newOutExpr <- repair(prevBody, prevFunction.returnType, outExpr)
         newFunDef = mkFunDef(newMain)()(stp => (Seq(), prevFunction.returnType, _ => newOutExpr))
         newProgram = InoxProgram(context, Seq(newFunDef), allConstructors)
    } yield (newProgram, newMain)
  }

  @inline def castOrFail[A, B <: A](a: A): B =
    a.asInstanceOf[B]

  /** Will try its best to transform prevOutExpr so that it produces newOut or at least incorporates the changes.
    * @param function An expression that computed the value before newOut
    * @param newOut A *value* that prevOutExpr should produce
    **/
  def repair(function: Expr, functionType: Type, newOut: Expr)(implicit symbols: Symbols): Iterable[Expr] = {
    Stream(newOut) // Constant replacement
    /*function match {
      case Let(valdef, body, expr) =>


      case ADT(ADTType(tp, tpArgs), args) =>
        newOut match {
          case ADT(ADTType(tp2, tpArgs2), args2) if tp2 == tp && tpArgs2 == tpArgs => // Same type ! Maybe the arguments will change or move.
            val adt = castOrFail[ADTDefinition, ADTConstructor](symbols.adts(tp))
            val tadt = adt.typed(tpArgs)
            tadt.field
            Nil
          case a => // Another value in the type hierarchy. But Maybe sub-trees are shared !

            ???
          case _ => ???
        }

      case _ => ???
    }*/
  }
}
