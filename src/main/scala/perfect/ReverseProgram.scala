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
  import StringConcatExtended._
  type FunctionEntry = Identifier
  type ModificationSteps = Unit
  type OutExpr = Expr
  type Cache = HashMap[Expr, Expr]

  import Utils._
  import InoxConvertible._
  lazy val context = Context.empty.copy(options = Options(Seq(optSelectedSolvers(Set("smt-cvc4")))))

  import Utils.ifEmpty

  /** Main entry point to reverse a program.
    * @param outProg The output that the program should produce
    * @param prevIn The program to repair. May be empty, in which case it returns outProg
    * @return The program prevIn such that it locally produces the changes given by outProg */
  def put(outProg: ProgramFormula, prevIn: Option[Expr]): Stream[Expr] = {
    if(prevIn == None) {
      val outExpr = outProg.bodyDefinition.getOrElse(throw new Exception(s"Ill-formed program: $outProg"))
      return Stream(outExpr)
    }

    implicit val symbols = defaultSymbols.withFunctions(ReverseProgram.funDefs)
    implicit val cache = new Cache
    for { r <- repair(ProgramFormula(prevIn.get), outProg)
          ProgramFormula(newOutExpr, f) = r.insertVariables()                    /: Log.remaining_program
          assignments <- f.determinizeAll(exprOps.variablesOf(newOutExpr).toSeq) /:: Log.found_assignments
          finalNewOutExpr = exprOps.replaceFromSymbols(assignments, newOutExpr)  /: Log.final_expression
    } yield finalNewOutExpr
  }

  /** Alternative way of reversing a program.
    * @param outProg The output that the program should produce
    * @param prevIn The program to repair, along with assignment formulas. May be empty, in which case it returns outProg
    * @return The program prevIn such that it locally produces the changes given by outProg */
  def put(outProg: ProgramFormula, prevIn: ProgramFormula): Stream[ProgramFormula] = {
    implicit val symbols = defaultSymbols.withFunctions(ReverseProgram.funDefs)
    implicit val cache = new Cache
    for { r <- repair(prevIn, outProg) } yield r.insertVariables() /: Log.remaining_program
  }
    /** Reverses a parameterless function, if possible.*/
  def putPf(outProg: ProgramFormula, prevIn: Option[(InoxProgram, FunctionEntry)]): Iterable[(InoxProgram, FunctionEntry)] = {
    val newMain = FreshIdentifier("main")
    put(outProg, prevIn.map{ case (prevProgram, prevFunctionEntry) =>
      val prevFunction = prevProgram.symbols.functions.getOrElse(prevFunctionEntry, return Nil)
      prevFunction.fullBody
    }).map{ finalNewOutExpr =>
      implicit val symbols = prevIn.map(_._1.symbols).getOrElse(defaultSymbols)
      val newFunDef = mkFunDef(newMain)()(stp => (Seq(), finalNewOutExpr.getType, _ => finalNewOutExpr))
      val newProgram = InoxProgram(context, symbols.withFunctions(newFunDef::ReverseProgram.funDefs))
      (newProgram, newMain)
    }
    /*
    if(prevIn == None) {
      implicit val symbols = defaultSymbols
      val main = FreshIdentifier("main")
      val fundef = mkFunDef(main)()(stp => (Seq(), outExpr.getType, _ => outExpr))
      return Stream((InoxProgram(context, Seq(fundef), allConstructors), main))
    }
    val (prevProgram, prevFunctionEntry) = prevIn.get
    implicit val symbols = prevProgram.symbols

    val newMain = FreshIdentifier("main")
    implicit val cache = new HashMap[Expr, Expr]
    for { r <- repair(ProgramFormula(prevBody), outProg)
         ProgramFormula(newOutExpr, f) = r
         _ = Log("Remaining formula: " + f)
         _ = Log("Remaining expression: " + newOutExpr)
         assignments <- f.determinizeAll(exprOps.variablesOf(newOutExpr).toSeq.map(_.toVal))
         _ = Log("Found assignments: " + assignments)
         finalNewOutExpr = exprOps.replaceFromSymbols(assignments, newOutExpr)
         _ = Log("Final  expression: " + finalNewOutExpr)
         newFunDef = mkFunDef(newMain)()(stp => (Seq(), prevFunction.returnType, _ => finalNewOutExpr))
         newProgram = InoxProgram(context, symbols.withFunctions(Seq(newFunDef)))
    } yield (newProgram, newMain)*/
  }

  def simplify(expr: Expr)(implicit cache: Cache, symbols: Symbols): Expr = {
    if(exprOps.variablesOf(expr).isEmpty) {
      evalWithCache(expr)
    } else expr
  }

  /** Eval function. Uses a cache normally. Does not evaluate already evaluated expressions. */
  def evalWithCache(expr: Expr)(implicit cache: Cache, symbols: Symbols) = cache.getOrElseUpdate(expr, {
    expr match {
      case l:Lambda => expr
      case _ =>
        import evaluators._
        val p = InoxProgram(context, symbols)
        val evaluator = LambdaPreservingEvaluator(p)
        evaluator.eval(expr) match {
          case EvaluationResults.Successful(e) => e
          case m => throw new Exception(s"Could not evaluate: $expr, got $m")
        }
    }
  })

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

  val semanticLenses: semanticlenses.SemanticLens =
    PatternMatch.Lens andThen
      PatternReplace.Lens andThen
      ListInsert.Lens andThen
      PasteVariable.Lens andThen
      StringInsert.Lens andThen
      perfect.lenses.SetLens andThen
      perfect.lenses.MapDataLens

  /** Will try its best to transform prevOutExpr so that it produces newOut or at least incorporates the changes.
    * Basically, we solve the problem:
    *  let variables = values in function = newOut
    * by trying to change the variables values, or the function body itself.
    *
    * @param program An expression that computed the value before newOut, and the formula contains the current mappings.
    * @param newOutProgram A ProgramFormula resulting from the action of the user on the datat.
    *               Either a literal value that should be produced by function,
    *               or a variable, in which case the result will have in the formula a constraint over this variable,
    *               Or an expression with constrained free variables to denote a clone-and-paste or many other things.
    * @return A set of possible expressions, along with a set of possible assignments to input variables.
    **/
  def repair(program: ProgramFormula, newOutProgram: ProgramFormula)
            (implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    val ProgramFormula(function, functionFormula) = program
    val ProgramFormula(newOut, newOutFormula) = newOutProgram
    val currentValues = functionFormula.known
    val stackLevel = Thread.currentThread().getStackTrace.length
    Log(s"\n@repair$stackLevel(\n  $program\n, $newOutProgram)")
    if(function == newOut) return { Log("@return original without constraints");
      Stream(program.assignmentsAsOriginals())
    }

    val semanticOriginalLens = semanticLenses andThen DefaultLens

    val finalRepair =
      ((TreeWrap.Lens andThen TreeUnwrap.Lens) andThen (TreeModification.Lens andThen
      ValueLens)) andThen {
        if (program.isWrappingLowPriority) {
          semanticOriginalLens interleave MaybeWrappedSolutions
        } else {
          MaybeWrappedSolutions interleave semanticOriginalLens
        }
      }
    finalRepair.put(program, newOutProgram) #:::
      {Log(s"Finished repair$stackLevel"); Stream.empty[ProgramFormula]}  /:: Log.prefix(s"@return for repair$stackLevel(\n  $program\n, $newOutProgram):\n~>")
  }
}