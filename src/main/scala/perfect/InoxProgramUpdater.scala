package perfect

object InoxProgramUpdater extends core.ProgramUpdater
    with core.ContExps
    with core.Lenses
    with lenses.ShapeLenses
    with lenses.ValueLenses
    with core.predef.InvocationLenses
    with core.predef.ApplicationLenses
    with core.predef.LambdaLenses
    with core.predef.ListLenses
    with core.predef.UnificationLenses
    with core.predef.ListLibraryLenses
    with core.predef.AssociativeLenses
    with core.predef.StringConcatLenses
    with core.predef.DefaultLenses {

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

  def eval(expr: inox.trees.Expr)(implicit symbols: Symbols): Either[inox.trees.Expr, String] = {
    import inox.evaluators._
    val p = inox.InoxProgram(context, symbols)
    val evaluator = LambdaPreservingEvaluator(p)
    evaluator.eval(expr) match {
      case EvaluationResults.Successful(e) => Left(e)
      case EvaluationResults.EvaluatorError(msg) => Right(msg)
      case EvaluationResults.RuntimeError(msg) => Right(msg)
      case m => Right("An error occurred. Sorry not to be able to give more information than " + m)
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
  def Assign(v: Variable, e: Expr, body: Expr): Expr = inox.trees.Let(v.toVal, e, body)
  def exists(f: Expr => Boolean)(e: Expr): Boolean = exprOps.exists(f)(e)
  def isValue(e: Expr): Boolean = perfect.Utils.isValue(e)
  def isVar(e: Expr): Boolean = e.isInstanceOf[Variable]
  def postMap(f: Expr => Option[Expr])(e: Expr): Expr = exprOps.postMap(f)(e)
  def preMap(f: Exp => Option[Exp],recursive: Boolean)(e: Exp): Exp = exprOps.preMap(f, recursive)(e)

  // Members declared in perfect.core.predef.ApplicationLenses
  def buildApplication(lambda: Exp, args: Seq[Exp]): Exp = inox.trees.Application(lambda, args)
  def extractApplication(e: Exp): Option[(Exp, Seq[Exp])] = e match {
    case inox.trees.Application(lambda, args) => Some((lambda, args))
    case _ => None
  }

  // Members declared in perfect.core.predef.AsInstanceOfLenses
  def extractAsInstanceOf(e: Exp): Option[(Exp, Exp => Exp)] = e match {
    case inox.trees.AsInstanceOf(e, tpe) => Some((e, x => inox.trees.AsInstanceOf(x, tpe)))
    case _ => None
  }

  // Members declared in perfect.core.predef.IfLenses
  def buildIf(cond: Exp,thn: Exp,elz: Exp): Exp = inox.trees.IfExpr(cond, thn, elz)
  def extractIf(e: Exp): Option[(Exp, Exp, Exp)] = e match {
    case inox.trees.IfExpr(cond, thn, elz) => Some((cond, thn, elz))
    case _ => None
  }

  // Members declared in perfect.core.predef.LambdaLenses
  def buildLambda(v: Seq[Var],body: Exp): Exp = inox.trees.Lambda(v.map(_.toVal), body)
  def extractLambda(e: Exp): Option[(Seq[Var], Exp, Exp => Exp)] = e match {
    case inox.trees.Lambda(vds, body) => Some((vds.map(_.toVariable), body, x => inox.trees.Lambda(vds, body)))
    case _ => None
  }

  // Members declared in perfect.core.predef.LetLenses
  def buildLet(v: Var,assigned: Exp,body: Exp): Exp = inox.trees.Let(v.toVal, assigned, body)
  def extractLet(e: Exp): Option[(Var, Exp, Exp)] = e match {
    case inox.trees.Let(v, thn, elz) => Some((v.toVariable, thn, elz))
    case _ => None
  }

  // Members declared in perfect.core.FunctionInvocationLenses
  def extractInvocation(e: Exp)(implicit cache: Cache, symbols: Symbols): Option[(Seq[Exp], Seq[Exp] => Exp)] = e match {
    case inox.trees.FunctionInvocation(id, tpe, args) => Some((args, newArgs => inox.trees.FunctionInvocation(id, tpe, newArgs)))
    case _ => None
  }

  // Members declared in perfect.core.predef.ListLenses
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
  /** Returns the default value of the unique argument of the lambda, */
  def extractLambdaDefaultArgument(e: Exp): Option[Exp] = e match {
    case inox.trees.Lambda(Seq(vd), body) => Some(perfect.Utils.defaultValue(vd.tpe))
    case _ => None
  }
  /** Returns an "unknown" fresh variable matching the type of the lambda's first argument*/
  def extractLambdaUnknownVar(e: Exp): Option[Var] = e match {
    case inox.trees.Lambda(Seq(vd), body) => Some(Variable(FreshIdentifier("unknown", true), vd.tpe, Set()))
    case _ => None
  }


  import perfect.semanticlenses.{ListInsertGoal, TreeModificationGoal, PasteVariableGoal, PatternReplaceGoal, PatternMatchGoal, StringInsertGoal, TreeUnwrapGoal, TreeWrapGoal}

  /** Returns the head, the tail and a way to build a list from a sequence of elements. */
  def extractCons(e: Exp): Option[(Exp, Exp, List[Exp] => Exp)] = e match {
    case inox.trees.ADT(ADTType(perfect.Utils.cons, Seq(tpe)), Seq(head, tail)) =>
      Some((head, tail, x => perfect.ListLiteral(x, tpe)))
    case _ => None
  }

  /** Returns the before, inserted and after fields of a ListInsert, along with
    * - A way to build a list from a list of elements and possibly a tail
    * - A way to build a ListInsertgoal again*/
  def extractListInsertGoal(e: Exp): Option[(List[Exp], List[Exp], List[Exp],
    (List[Exp], Option[Exp]) => Exp,
    (List[Exp], List[Exp], List[Exp]) => Exp)] = e match {
    case ListInsertGoal(tpe, left, inserted, right) =>
      Some((left, inserted, right,
        (x, s) => s.map(tail => perfect.ListLiteral.concat(perfect.ListLiteral(x, tpe), tail)).getOrElse(perfect.ListLiteral(x, tpe)),
        (left, inserted, right) => ListInsertGoal(tpe, left, inserted, right)
      ))
    case _ => None
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
    case inox.trees.ADT(tpe, args) => Some((args, x => inox.trees.ADT(tpe, args)))
    case _ => None
  }

  def extractADTSelector(e: Exp)(implicit symbols: Symbols): Option[(Exp, Exp => Exp, Seq[Var], Int)]  = e match {
    case as@inox.trees.ADTSelector(expr, id) =>
      val constructor = as.constructor.get
      val fields = constructor.fields
      val index = as.selectorIndex
      val vrs = fields.map { fd => Variable(FreshIdentifier("x", true), fd.getType, Set()) }
      Some((expr, x => inox.trees.ADTSelector(x, id), vrs, index))
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

  /** In a map, can the output be transfered to the input, e.g. when adding a new row in a mkString mapped with a prefix. */
  def canPushInsertedOutputToInput(output: Exp, lambda: Exp)(implicit symbols: Symbols): Boolean = {
    lambda match {
      case inox.trees.Lambda(Seq(vd), body) =>
        vd.tpe == body.getType && output == StringLiteral("")
      case _ => false
    }
  }

  /** Returns the original tree, the modified subtree, and instead of a path,
    * an index indicating where the next change should happen with a way to rebuild the goal with the new original subtree */
  def extractTreeModificationGoal(goal: Exp)(implicit symbols: Symbols):
      Option[(Exp, Exp, Option[(Int, Exp)])] = goal match {
    case TreeModificationGoal(tpeGlobal, tpeLocal, original, modified, l) =>
      Some((original, modified, l match {
        case head::tail =>
          original match {
            case l@inox.trees.ADT(ADTType(adtid, tps), args) =>
              symbols.adts(adtid) match {
                case f: ADTConstructor =>
                  val i = f.selectorID2Index(head)
                  val newOriginal = args(i)
                  Some((i, TreeModificationGoal(newOriginal.getType, tpeLocal, newOriginal, modified, tail)))
                case _ => return None
              }
            case _ => return None
          }
        case _ => None
      }))
    case _ => None
  }

  def extractTreeUnwrapGoal(e: Exp)(implicit symbols: Symbols): Option[(Exp, Option[(Int, Exp)])] = e match {
    case TreeUnwrapGoal(tpe, original, path) =>
      path match {
        case Nil =>
          Some((original, None))
        case head :: tail =>
          original match {
            case l@inox.trees.ADT(ADTType(adtid, tps), args) =>
              symbols.adts(adtid) match {
                case f: ADTConstructor =>
                  val i = f.selectorID2Index(head)
                  val newOriginal = args(i)
                  Some((original, Some((i, TreeUnwrapGoal(newOriginal.getType, newOriginal, tail)))))
                case _ => None
              }
            case _ => None
          }
      }
    case _ => None
  }

  def extractTreeWrapGoal(e: Exp): Option[(Exp, Exp => Exp)] = e match {
    case TreeWrapGoal(original, wrapper) => Some((original, wrapper))
    case _ => None
  }

  // Members declared in perfect.lenses.PasteVariableLenses
  def buildPasteStringVarGoal(left: String,v: Var,v_value: String,right: String,direction: perfect.core.predef.AssociativeInsert.InsertDirection): Exp = {
    PasteVariableGoal(left, v, v_value, right, direction)
  }
  def extractPasteStringVarGoal(e: Exp): Option[(String, Var, String, String, perfect.core.predef.AssociativeInsert.InsertDirection)] = {
    PasteVariableGoal.unapply(e)
  }

  // Members declared in perfect.lenses.PatternMatchLenses
  def buildPatternMatchGoal(pattern: Exp,vars: List[(Var, Exp)],forClone: Boolean): Exp =
    PatternMatchGoal(pattern, vars, forClone)
  def extractPatternMatchGoal(e: Exp): Option[(Exp, List[(Var, Exp)], Boolean)] =
    PatternMatchGoal.unapply(e)

  // Members declared in perfect.lenses.PatternReplaceLenses
  def buildPatternReplaceGoal(pattern: Exp,variables: List[(Var, Exp)],after: Exp): Exp =
    PatternReplaceGoal(pattern, variables, after)
  def extractPatternReplaceGoal(e: Exp): Option[(Exp, List[(Var, Exp)], Exp)] =
    PatternReplaceGoal.unapply(e)

  // Members declared in perfect.lenses.StringConcatLenses
  def buildStringConcat(left: Exp,right: Exp): Exp = inox.trees.StringConcat(left, right)
  def buildStringConcatSimplified(left: Exp,right: Exp): Exp = {
    new StringConcatExtended.AugmentedSubExpr(left).+<>&(right)
  }
  def extractStringConcat(e: Exp): Option[(Exp, Exp)] = e match {
    case inox.trees.StringConcat(a, b) => Some((a, b))
    case _ => None
  }

  // Members declared in perfect.lenses.StringInsertLenses
  def buildStringInsertGoal(left: String,inserted: String,right: String,direction: perfect.core.predef.AssociativeInsert.InsertDirection): Exp = {
    StringInsertGoal(left, inserted, right, direction)
  }
  def extractStringInsertGoal(e: Exp): Option[(String, String, String, perfect.core.predef.AssociativeInsert.InsertDirection)] = {
    StringInsertGoal.unapply(e)
  }

  // Members declared in perfect.core.predef.StringLenses
  def buildStringLiteral(e: String): Exp = inox.trees.StringLiteral(e)
  def extractStringliteral(e: Exp): Option[String] = e match {
    case inox.trees.StringLiteral(s) => Some(s)
    case _ => None
  }


  // Lenses which do not need the value of the program to invert it.
  val shapeLenses: SemanticLens =
    combine(ShortcutGoal(
      Map(TreeWrapGoal.id -> TreeWrapLens,
      TreeUnwrapGoal.id -> TreeUnwrapLens,
      TreeModificationGoal.id -> TreeModificationLens),
      (x: Exp) => x match { case FunctionInvocation(id, _, _) => Some(id) case _ => None } ),
    ValueLens)

  def functionInvocationLens: SemanticLens =
    ShortcutLens(Map[inox.Identifier, SemanticLens](
      perfect.Utils.filter -> FilterLens,
      perfect.Utils.map -> MapLens,
      perfect.Utils.dummyStringConcat -> StringConcatLens.named("stringConcat")
      // TODO: Add all lenses from lenses.Lenses
      /*MapLens,
      ListConcatLens,
      FlattenLens,
      FlatMapLens,
      SplitEvenLens,
      MergeLens,
      SortWithLens,
      MkStringLens,
      RecLens2*/
    ), {
      case FunctionInvocation(id, _, _) => Some(id)
      case StringConcat(_, _) =>
        println("strConcat ")
        Some(perfect.Utils.dummyStringConcat)
      case e =>
        println("No match for function invocation " + e)
        None
    }).named("Dispatch function invocation")
  import perfect.lenses._

// Lenses which need the value of the program to invert it.
  val semanticLenses: SemanticLens = valueLenses // andThen

  debug = true

  val lens = combine(
    NoChangeLens.named("No Change?"),
    ConstantReplaceLens.named("ConstantReplace"),
    shapeLenses.named("Shape?"),
    /*WrapperLens(*/semanticLenses.named("Semantic?") andThen defaultLens.named("default")/*, MaybeWrappedSolutions)*/
  )
}


