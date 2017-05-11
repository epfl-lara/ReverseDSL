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

  /** Transforms an expression bottom-up */
  def postMap(f: Exp => Option[Exp])(e: Exp): Exp

  /** Returns true if a sub-tree of e satisfies the predicate f.*/
  def exists(f: Exp => Boolean)(e: Exp): Boolean

  /** Default symbols */
  implicit def symbols: Symbols

  /** All free variables of an expression */
  def freeVariables(e: Exp): Set[Var]

  /** Freshen a variable, i.e. gives it a new name. */
  def freshen(a: Var, others: Var*): Var

  /** The main reversion lens */
  def lens: SemanticLens

  type Cache = HashMap[Exp, Exp]

  /** Obtain all possible assignments from the formula Cont for the given free variables */
  def determinizeAll(cont: Cont)(freeVariables: Seq[Var] = cont.varsToAssign.toSeq)(implicit symbols: Symbols, cache: Cache): Stream[Map[Var, Exp]]

  /** Evaluates a given closed expression */
  def eval(expr: Exp)(implicit symbols: Symbols): Either[Exp, String]

  //////////// Concrete members
  /** Eval function. Uses a cache normally. Does not evaluate already evaluated expressions. */
  def maybeEvalWithCache(expr: Exp)(implicit cache: Cache, symbols: Symbols): Option[Exp] = {
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
  /** Automatic simplification of EXPR1 && EXPR2 if one is true.*/
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

  var debug: Boolean = false

  def repair(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
    if(!Log.activate) {
      theLens.put(in, out)
    } else {
      val stackLevel = Thread.currentThread().getStackTrace.length
      Log(s"\n@repair$stackLevel(\n  $in\n, $out)")

      theLens.put(in, out) #:::
        {Log(s"Finished repair$stackLevel"); Stream.empty[ContExp]}  /:: Log.prefix(s"@return for repair$stackLevel(\n  $in\n, $out):\n~>")
    }
  }
}
