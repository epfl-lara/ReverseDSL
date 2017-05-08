package perfect

import inox.Identifier
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import perfect.ReverseProgram.Cache
import perfect.Utils.isValue
import perfect.semanticlenses._
import perfect.wraplenses.MaybeWrappedSolutions
import perfect.lenses.ValueLens
import scala.collection.mutable.{HashMap, ListBuffer}

/**
  * Created by Mikael on 03/03/2017.
  */
object ReverseProgram extends lenses.Lenses {
  type FunctionEntry = Identifier
  type ModificationSteps = Unit
  type OutExpr = Expr
  type Cache = HashMap[Expr, Expr]

  import Utils._
  import InoxConvertible._
  lazy val context = Context.empty.copy(options = Options(Seq(optSelectedSolvers(Set("smt-cvc4")))))

  import Utils.ifEmpty

  /** Main entry point to reverse a program.
    * @param out The output that the program should produce
    * @param in The program to repair. May be empty, in which case it returns out
    * @return The program in such that it locally produces the changes given by out */
  def put(in: Option[Expr], out: ProgramFormula): Stream[Expr] = {
    if(in == None) {
      val outExpr = out.bodyDefinition.getOrElse(throw new Exception(s"Ill-formed program: $out"))
      return Stream(outExpr)
    }

    implicit val symbols = defaultSymbols.withFunctions(ReverseProgram.funDefs)
    implicit val cache = new Cache
    for { r <- repair(ProgramFormula(in.get), out)
          ProgramFormula(newOutExpr, f) = r.insertVariables()                    /: Log.remaining_program
          assignments <- f.determinizeAll(exprOps.variablesOf(newOutExpr).toSeq) /:: Log.found_assignments
          finalNewOutExpr = exprOps.replaceFromSymbols(assignments, newOutExpr)  /: Log.final_expression
    } yield finalNewOutExpr
  }

  /** Alternative way of reversing a program.
    * @param out The output that the program should produce
    * @param in The program to repair, along with assignment formulas. May be empty, in which case it returns out
    * @return The program in such that it locally produces the changes given by out */
  def put(in: ProgramFormula, out: ProgramFormula): Stream[ProgramFormula] = {
    implicit val symbols = defaultSymbols.withFunctions(ReverseProgram.funDefs)
    implicit val cache = new Cache
    for { r <- repair(in, out) } yield r.insertVariables() /: Log.remaining_program
  }

  /** Eval function. Uses a cache normally. Does not evaluate already evaluated expressions. */
  def maybeEvalWithCache(expr: Expr)(implicit cache: Cache, symbols: Symbols): Option[Expr] = {
    if(cache.contains(expr)) {
      Some(cache(expr))
    } else {
      import evaluators._
      val p = InoxProgram(context, symbols)
      val evaluator = LambdaPreservingEvaluator(p)
      evaluator.eval(expr) match {
        case EvaluationResults.Successful(e) =>
          cache(expr) = e
          Some(e)
        case m => Log(s"Could not evaluate: $expr, got $m")
          None
      }
    }
  }


  /** Returns an evaluator which preserves lambda shapes */
  def LambdaPreservingEvaluator(p: InoxProgram) = {
    import evaluators._
    new {
      val program: p.type = p
      val options = context.options
    } with LambdaPreservingEvaluator
      with HasDefaultGlobalContext with HasDefaultRecContext {
      val semantics: p.Semantics = p.getSemantics
    }
  }

  // Lenses which do not need the value of the program to invert it.
  val shapeLenses: semanticlenses.SemanticLens =
    ((TreeWrap.Lens andThen
      TreeUnwrap.Lens) andThen (
      TreeModification.Lens andThen
        ValueLens))

  // Lenses which need the value of the program to invert it.
  val semanticLenses: semanticlenses.SemanticLens =
      (PatternMatch.Lens andThen  // Stand-alone programs on how to repair the program for a given instruction
      PatternReplace.Lens) andThen
      (ListInsert.Lens andThen
      PasteVariable.Lens) andThen
      (StringInsert.Lens andThen
      perfect.lenses.SetLens) andThen // Matchers for Set and SetApply constructions
      (perfect.lenses.MapDataLens andThen // Matcher for FiniteMap and MapApply constructions
      ADTExpr.Lens) // Matcher for ADT and ADTSelector constructions.

  val lens = NoChangeLens andThen
    shapeLenses andThen WrapperLens(semanticLenses andThen DefaultLens, MaybeWrappedSolutions)

  /** Will try its best to transform in so that it produces out or at least incorporates the changes.
    * Entry point of all lenses.
    *
    * @param in An expression that computed the value before newOut, and the formula contains the current mappings.
    * @param out A ProgramFormula resulting from the action of the user on the datat.
    *            Either a literal value that should be produced by function,
    *            or a variable, in which case the result will have in the formula a constraint over this variable,
    *            Or an expression with constrained free variables to denote a clone-and-paste or many other things.
    * @return A set of possible expressions, along with a set of possible assignments to input variables.
    **/
  def repair(in: ProgramFormula, out: ProgramFormula)
            (implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    if(!Log.activate) {
      lens.put(in, out)
    } else {
      val stackLevel = Thread.currentThread().getStackTrace.length
      Log(s"\n@repair$stackLevel(\n  $in\n, $out)")

      lens.put(in, out) #:::
        {Log(s"Finished repair$stackLevel"); Stream.empty[ProgramFormula]}  /:: Log.prefix(s"@return for repair$stackLevel(\n  $in\n, $out):\n~>")
    }
  }
}