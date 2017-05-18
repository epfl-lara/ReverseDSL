package perfect.core

/**
  * Created by Mikael on 06/05/2017.
  */
import scala.collection.mutable.HashMap

/**
  * Created by Mikael on 06/05/2017.
  */
trait ProgramUpdater { self: ContExps with Lenses =>
  //////////////// Abstract members
  type Exp
  type Symbols
  type Var <: Exp

  def isValue(e: Exp): Boolean
  def isVar(e: Exp): Boolean

  /** Builds an equality constraint */
  def Equal(e1: Exp, e2: Exp): Exp
  /** Builds a conjunction of constraints*/
  def And(e1: Exp, e2: Exp): Exp

  /** Wrapper around a constraint which initially holds*/
  def Originally(e1: Exp): Exp

  /** Assigns a given variable to e inside a body */
  def Assign(v: Var, e: Exp, body: Exp): Exp

  /** Value of a true expression */
  def ExpTrue: Exp
  def ExpFalse: Exp

  /** For this expression, a way to obtain its sub-expressions and to rebuild it */
  def extractors(e: Exp): (Seq[Exp], Seq[Exp] => Exp)

  /** Which variables this expression binds*/
  def bindings(e: Exp): Set[Var]

  /** Default symbols */
  implicit def symbols: Symbols

  /** Freshen a variable, i.e. gives it a new name. */
  def freshen(a: Var, others: Var*): Var

  /** Creates a var from an expression with the given name */
  def varFromExp(name: String, e: Exp, showUniqueId: Boolean)(implicit symbols: Symbols): Var
  def varFromExp(name: String, e: Exp)(implicit symbols: Symbols): Var = varFromExp(name, e, false)

  /** The main reversion lens */
  def lens: SemanticLens

  type Cache = HashMap[Exp, Exp]

  /** Obtain all possible assignments from the formula Cont for the given free variables */
  def determinizeAll(cont: Cont)(freeVariables: Seq[Var] = cont.varsToAssign.toSeq)(implicit symbols: Symbols, cache: Cache): Stream[Map[Var, Exp]]

  /** Evaluates a given closed expression */
  def eval(expr: Exp)(implicit symbols: Symbols): Either[Exp, String]

  //////////// Concrete members
  def replaceFromVars(substs: Map[Var, Exp], b: Exp) = {
    postMap {
      case Var(v) => substs.get(v)
      case _ => None
    }(b)
  }

  /** Transforms an expression bottom-up */
  def postMap(f: Exp => Option[Exp])(e: Exp): Exp = {
    val rec = postMap(f) _
    val (exprs, builder) = extractors(e)
    val newExprs = exprs map rec
    val r = if(newExprs != exprs) builder(newExprs) else e
    f(r).getOrElse(r)
  }

  /** Transforms an expression top-down */
  def preMap(f: Exp => Option[Exp], recursive: Boolean = false)(e: Exp): Exp = {
    val newE = f(e).getOrElse(e)
    if(newE != e && recursive) return preMap(f, recursive)(newE)
    val (exprs, builder) = extractors(newE)
    val newExprs = exprs map preMap(f)
    if(newExprs != exprs) builder(newExprs) else newE
  }

  /** Returns true if a sub-tree of e satisfies the predicate f.*/
  def exists(f: Exp => Boolean)(e: Exp): Boolean = {
    if(f(e)) return true
    val (exprs, builder) = extractors(e)
    exprs.exists(exists(f))
  }

  /** All free variables of an expression */
  def freeVariables(e: Exp): Set[Var] = {
    e match {
      case Var(v) => Set(v)
      case _ =>
        val (exprs, builder) = extractors(e)
        exprs.toSet.flatMap(freeVariables) -- bindings(e)
    }
  } /: perfect.Log.prefix(s"freeVariables($e) = ")


  /** Eval function. Uses a cache normally. Does not evaluate already evaluated expressions. */
  def maybeEvalWithCache(expr: Exp)(implicit symbols: Symbols, cache: Cache): Option[Exp] = {
    if(cache.contains(expr)) {
      Some(cache(expr))
    } else {
      eval(expr) match {
        case s@Left(v) => cache(expr) = v
          Some(v)
        case s@Right(_) => None
      }
    }
  }

  implicit class AugmentedExp(e1: Exp) {
    def ===(e2: Exp) = Equal(e1, e2)
  }
  /* Automatic simplification of EXPR1 && EXPR2 if one is true.*/
  implicit class BooleanSimplification(f: Exp) {
    @inline def &<>&(other: Exp): Exp =
      if(other == ExpTrue)  f
      else if(other == ExpFalse) other
      else if(f == ExpTrue) other
      else if(f == ExpFalse) f
      else And(f, other)
  }

  val Utils = new perfect.core.Utils(self)

  /** Replaces variables by expressions */
  def replace(m: Map[Var, Exp], e: Exp) = {
    postMap{
      case Var(e) => m.get(e)
      case _ => None
    }(e)
  }

  object Var {
    def unapply(e: Exp): Option[Var] = if(isVar(e)) Some(e.asInstanceOf[Var]) else None
  }

  import perfect.Log

  /** Main entry point to reverse a program.
    * @param out The output that the program should produce
    * @param in The program to repair. May be empty, in which case it returns out
    * @return The program in such that it locally produces the changes given by out */
  def put(in: Option[Exp], out: ContExp): Stream[Exp] = {
    if(in == None) {
      val outExpr = out.bodyDefinition.getOrElse(throw new Exception(s"Ill-formed program: $out"))
      return Stream(outExpr)
    }

    implicit val cache = new Cache
    for { r <- repair(ContExp(in.get), out)
          ContExp(newOutExpr, f) = r.insertVariables()                       /: Log.remaining_program
          assignments <- determinizeAll(f)(freeVariables(newOutExpr).toSeq) /:: Log.found_assignments
          finalNewOutExpr = replace(assignments, newOutExpr)  /: Log.final_expression
    } yield finalNewOutExpr
  }

  /** Alternative way of reversing a program.
    * @param out The output that the program should produce
    * @param in The program to repair, along with assignment formulas. May be empty, in which case it returns out
    * @return The program in such that it locally produces the changes given by out */
  def put(in: ContExp, out: ContExp): Stream[ContExp] = {
    implicit val cache = new Cache
    for { r <- repair(in, out) } yield r.insertVariables() /: Log.remaining_program
  }

  lazy val theLens = lens

  def debug: Boolean = false

  var repairid = 1

  def repair(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
    if(!Log.activate) {
      theLens.put(in, out)
    } else {
      val stackLevel = {repairid += 1; repairid} // Thread.currentThread().getStackTrace.length
      val instr = in.toString.replaceAll("\n", "\n  ")
      val outstr = out.toString.replaceAll("\n", "\n  ")
      Log(s"\n@repair$stackLevel(\n  $instr\n, $outstr)")

      theLens.put(in, out) #:::
        {Log(s"Finished repair$stackLevel"); Stream.empty[ContExp]}  /:: Log.prefix(s"@return for repair$stackLevel(\n  $instr\n, $outstr):\n~>")
    }
  }
}
