package perfect

object InoxProgramUpdater extends core.ProgramUpdater
    with core.ContExps
    with core.Lenses
    with lenses.ShapeLenses
    with lenses.ValueLenses
    with core.predef.InvocationLenses
    with core.predef.UnificationLenses
    with core.predef.ListLenses
    with core.predef.AssociativeLenses
    with lenses.StringConcatLenses {

  import inox.FreshIdentifier

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
        val input = Variable(FreshIdentifier("input"), tupleTypeWrap(freeVariables.map(_.getType)), Set())
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
  def freshen(a: Var, others: Var*): Var = {
    if(others.isEmpty) {
      a.freshen
    } else {
      Variable(FreshIdentifier(perfect.Utils.uniqueName(a.id.name, others.map(v => v.id.name).toSet)), a.tpe, Set())
    }
  }

  def mkStringVar(name: String, avoid: Var*): Var = {
    Variable(FreshIdentifier(perfect.Utils.uniqueName(name, avoid.map(_.id.name).toSet)), StringType, Set())
  }

  def isSameInvocation(e: Expr, g: Expr)(implicit cache: Cache, symbols: Symbols) = e match {
    case FunctionInvocation(f, tpes, _) => g match {
      case FunctionInvocation(f2, tpes2, _) => f == f2 && tpes == tpes2
      case _ => false
    }
    case _ => false
  }

  // Members declared in perfect.core.predef.MapDataLenses
  def buildMapApply(e: Exp,g: Exp): Exp = inox.trees.MapApply(e, g)
  def extractMap(e: Exp)(implicit symbols: Symbols): Option[(Seq[(Exp, Exp)], Exp, (Seq[(Exp, Exp)], Exp) => Exp)] = e match {
    case FiniteMap(pairs, default, keyt, valuet) => Some((pairs, default, (pairs, default) => FiniteMap(pairs, default, keyt, valuet)))
    case _ => None
  }
  def extractMapApply(e: Exp)(implicit symbols: Symbols): Option[(Exp, Exp, String => Var)] = e match {
    case MapApply(mpBuilder, mpArg) =>
      mpBuilder.getType match {
        case MapType(keyt, valuet) =>
          Some((mpBuilder, mpArg, name => Variable(FreshIdentifier(name, true), valuet, Set())))
        case _ => None
      }
    case _ => None
  }

  // Members declared in perfect.core.predef.SetLenses
  def extractSet(e: Exp): Option[(Seq[Exp], Seq[Exp] => Exp)] = e match {
    case inox.trees.FiniteSet(elems, base) => Some((elems, elems => inox.trees.FiniteSet(elems, base)))
    case _ => None
  }
  def extractSetAdd(e: Exp): Option[(Exp, Exp)] = e match {
    case inox.trees.SetAdd(set, elem) => Some((set, elem))
    case _ => None
  }
  def buildSetAdd(set: Exp, elem: Exp): Exp = inox.trees.SetAdd(set, elem)

  // Members declared in perfect.core.predef.ADTLenses
  /** Returns the arguments of the ADT and a builder for it.*/
  def extractADT(e: Exp): Option[(Seq[Exp], Seq[Exp] => Exp)] = e match {
    case inox.trees.ADT(tpe, args) => Some((args, x => ADT(tpe, args)))
    case _ => None
  }

  def extractADTSelector(e: Exp)(implicit symbols: Symbols): Option[(Exp, Exp => Exp, Seq[Var], Int)]  = e match {
    case as@inox.trees.ADTSelector(expr, id) =>
      val constructor = as.constructor.get
      val fields = constructor.fields
      val index = as.selectorIndex
      val vrs = fields.map { fd => Variable(FreshIdentifier("x", true), fd.getType, Set()) }
      Some((expr, x => ADTSelector(x, id), vrs, index))
    case _ => None
  }
  /** Returns true if e and g are two instances of the same ADT type */
  def isSameADT(e: Exp, g: Exp): Boolean = e match {
    case inox.trees.ADT(tpe, _) => g match {
      case inox.trees.ADT(tpe2, _) => tpe == tpe2
      case _ => false
    }
    case _ => false
  }

  // Lenses which do not need the value of the program to invert it.
  val shapeLenses: SemanticLens =
    combine(TreeWrapLens,
      TreeUnwrapLens,
      TreeModificationLens,
      ValueLens)

  def functionLenses = Map[inox.Identifier, SemanticLens](
    perfect.Utils.filter -> FilterLens
    // TODO: Add all lenses from lenses.Lenses
    /*MapLens,
    ListConcatLens,
    FlattenLens,
    FlatMapLens,
    StringConcatLens,
    SplitEvenLens,
    MergeLens,
    SortWithLens,
    MkStringLens,
    RecLens2*/
  )

  def functionInvocationLens: SemanticLens =
    ShortcutLens(functionLenses, {
      case FunctionInvocation(id, _, _) => Some(id)
      case _ => None
    })
  import perfect.lenses._

// Lenses which need the value of the program to invert it.
  val semanticLenses: SemanticLens = valueLenses // andThen



  val lens = NoChangeLens andThen
    shapeLenses andThen /*WrapperLens(*/semanticLenses/* andThen DefaultLens, MaybeWrappedSolutions)*/

}


