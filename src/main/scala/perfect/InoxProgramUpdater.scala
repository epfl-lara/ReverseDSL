package perfect

object InoxProgramUpdater extends core.ProgramUpdater
    with core.ContExps
    with core.Lenses
    with lenses.ShapeLenses
    with core.predef.InvocationLenses
    with core.predef.ListLenses {
  type Exp = inox.trees.Expr
  type Symbols = inox.trees.Symbols
  type Var = inox.trees.Variable

  def Equal(e1: Exp, e2: Exp): Exp = inox.trees.Equals(e1, e2)

  /** Wrapper around a constraint which initially holds */
  override def Originally(e1: InoxProgramUpdater.Exp): InoxProgramUpdater.Exp = {
    inox.trees.FunctionInvocation(perfect.Utils.original, Seq(), Seq(e1))
  }

  /** Value of a true expression */
  override def ExpTrue: InoxProgramUpdater.Exp = inox.trees.BooleanLiteral(true)

  /** Builds a conjunction of constraints */
  override def And(e1: InoxProgramUpdater.Exp, e2: InoxProgramUpdater.Exp): InoxProgramUpdater.Exp = {
    val inox.trees.TopLevelAnds(a_e1) = e1
    val inox.trees.TopLevelAnds(a_e2) = e2
    inox.trees.andJoin((a_e1 ++ a_e2).distinct)
  }

  override def ExpFalse: InoxProgramUpdater.Exp = inox.trees.BooleanLiteral(false)

  /** All free variables of an expression */
  def freeVariables(e: inox.trees.Expr): Set[inox.trees.Variable] = inox.trees.exprOps.variablesOf(e)

  lazy val context = inox.Context.empty.copy(options = inox.Options(Seq(inox.optSelectedSolvers(Set("smt-cvc4")))))

  implicit def symbols = perfect.Utils.defaultSymbols.withFunctions(lenses.Lenses.funDefs)

  /** Eval function. Uses a cache normally. Does not evaluate already evaluated expressions. */
  def maybeEvalWithCache(expr: inox.trees.Expr)(implicit cache: Cache, symbols: Symbols): Option[inox.trees.Expr] = {
    if(cache.contains(expr)) {
      Some(cache(expr))
    } else {
      import inox.evaluators._
      val p = inox.InoxProgram(context, symbols)
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
  def LambdaPreservingEvaluator(p: inox.InoxProgram) = {
    import inox.evaluators._
    new {
      val program: p.type = p
      val options = context.options
    } with LambdaPreservingEvaluator
      with HasDefaultGlobalContext with HasDefaultRecContext {
      val semantics: p.Semantics = p.getSemantics
    }
  }

  import inox.trees._
  import inox.trees.dsl._

  /** Obtain all possible assignments from the formula Cont for the given free variables */
  def determinizeAll(cont: Cont)(freeVariables: Seq[Var] = cont.varsToAssign.toSeq)(implicit symbols: Symbols, cache: Cache): Stream[Map[Var, Exp]] = {
    perfect.Log(s"Trying to get all solutions for ${cont.varsToAssign} of \n" + cont)
    val simplified = Cont.inlineSimpleConts(cont)
    perfect.Log(s"Simplified: $simplified")
    val streamOfSolutions = simplified.partialAssignments match {
      case Some((wrapper, remaining)) if remaining.forall(x => x._2 == AllValues) =>
        maybeEvalWithCache(wrapper(tupleWrap(freeVariables)))(cache, symbols).toStream
      case e =>
        if(e.nonEmpty) Log(s"Warning: some equations could not be simplified: $e")
        val input = Variable(inox.FreshIdentifier("input"), tupleTypeWrap(freeVariables.map(_.getType)), Set())
        val constraint = InoxConstraint(input === tupleWrap(freeVariables) &<>& simplified.constraints &<>&
          and(simplified.known.toSeq.map{ case (k, v) => v.getConstraint(k)}: _*))
        Log(s"Solving as $constraint")
        constraint.toStreamOfInoxExpr(input)
    }
    streamOfSolutions.map {
      case Tuple(args) => freeVariables.zip(args).map{ case (fv: Var, expr: Exp) => fv -> expr }.toMap
      case e if freeVariables.length == 1 => Map(freeVariables.head -> e)
      case UnitLiteral() if freeVariables.length == 0 => Map[Var, Exp]()
      case e =>
        throw new Exception(s"Other unexpected solution: $e")
    }
  }
  // Members declared in perfect.core.ContExps
  def commands: List[ContExpCommand] = {
    // TODO: Add commands
    List()
  }

  // Members declared in perfect.core.ProgramUpdater
  def Assign(v: Variable, e: Expr, body: Expr): Expr = Let(v.toVal, e, body)
  def exists(f: Expr => Boolean)(e: Expr): Boolean = exprOps.exists(f)(e)
  def isValue(e: Expr): Boolean = perfect.Utils.isValue(e)
  def isVar(e: Expr): Boolean = e.isInstanceOf[Variable]
  def postMap(f: Expr => Option[Expr])(e: Expr): Expr = exprOps.postMap(f)(e)

  // Members declared in perfect.core.predef.ListLenses
  def Application(a: Exp,b: Seq[Exp]): Exp = inox.trees.Application(a, b)
  def extractInvocation(e: Exp)(implicit cache: Cache, symbols: Symbols): Option[(Seq[Exp], Seq[Exp] => Exp)] = e match {
    case inox.trees.FunctionInvocation(id, tpe, args) => Some((args, newArgs => inox.trees.FunctionInvocation(id, tpe, newArgs)))
    case _ => None
  }
  def extractList(e: Exp): Option[(List[Exp], List[Exp] => Exp)] = e match {
    case perfect.ListLiteral(elements, builder) => Some((elements, builder))
    case _ => None
  }
  def freshen(a: Var): Var = a.freshen

  // Lenses which do not need the value of the program to invert it.
  val shapeLenses: SemanticLens =
    ((TreeWrapLens andThen
      TreeUnwrapLens) andThen (
      TreeModificationLens andThen
        ValueLens))

  val functions: List[SemanticLens] = List(
    FilterLens
  )
  val reversions = Map[inox.Identifier, SemanticLens](
    perfect.Utils.filter -> FilterLens
  )

  val functionInvocationLens: SemanticLens =
    ShortcutLens(reversions, {
      case FunctionInvocation(id, _, _) => Some(id)
      case _ => None
    })
  import perfect.lenses._
/*
  // Lenses which need the value of the program to invert it.
  val semanticLenses: semanticlenses.SemanticLens =
    (PatternMatch.Lens andThen  // Stand-alone programs on how to repair the program for a given instruction
      PatternReplace.Lens) andThen
      (ListInsert.Lens andThen
        PasteVariable.Lens) andThen
      (StringInsert.Lens andThen
        functionInvocationLens) andThen // Matcher for function invocation in out.
      (FunctionInvocationUnificationLens andThen // Unification of arguments for function invocation.
        SetLens) andThen // Matchers for Set and SetApply constructions
      (MapDataLens andThen // Matcher for FiniteMap and MapApply constructions
        ADTExpr.Lens) // Matcher for ADT and ADTSelector constructions.


  val lens = NoChangeLens andThen
    shapeLenses andThen WrapperLens(semanticLenses andThen DefaultLens, MaybeWrappedSolutions)*/

  val lens = ???
}


