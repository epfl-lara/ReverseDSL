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
    with core.predef.ListStringLibraryLenses
    with core.predef.AssociativeLenses
    with core.predef.StringConcatLenses
    with core.predef.ListConcatLenses
    with core.predef.DefaultLenses
    with core.predef.RecursiveLenses
    with core.predef.WrappedLenses
    with lenses.ListLibraryExtendedLenses{

  import inox.FreshIdentifier

  type Exp = inox.trees.Expr
  type Symbols = inox.trees.Symbols
  type Var = inox.trees.Variable

  def Equal(e1: Exp, e2: Exp): Exp = inox.trees.Equals(e1, e2)
  def extractEqual(e: Exp): Option[(Exp, Exp)] = e match {
    case inox.trees.Equals(e1, e2) => Some((e1, e2))
    case _ => None
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
  def extractors(e: inox.trees.Expr): (Seq[inox.trees.Expr], Seq[inox.trees.Expr] => inox.trees.Expr) =
    inox.trees.exprOps.Deconstructor.unapply(e).getOrElse((Seq(), _ => e))

  /** All sub-variables than an expression binds. */
  def bindings(e: Exp): Set[Var] = e match {
    case inox.trees.Lambda(vds, body) => vds.map(_.toVariable).toSet
    case inox.trees.Let(vd, expr, body) => Set(vd.toVariable)
    case _ => Set.empty[Var]
  }

  lazy val context = inox.Context.empty.copy(options = inox.Options(Seq(inox.optSelectedSolvers(Set("smt-cvc4")))))

  implicit def symbols = perfect.Utils.defaultSymbols.withFunctions(lenses.Lenses.funDefs)

  def eval(expr: Exp)(implicit symbols: Symbols): Either[Exp, String] = {
    eval(ContExp(expr)) match {
      case Left(x) => Left(x.exp)
      case Right(x) => Right(x)
    }
  }
  override def eval(expr: ContExp)(implicit symbols: Symbols): Either[ContExp, String] = {
    import inox.evaluators._
    val p = inox.InoxProgram(context, symbols)
    val evaluator = LambdaPreservingEvaluator(p)
    try { evaluator.eval(expr.exp) match {
      case EvaluationResults.Successful(e) => Left(ContExp(e))
      case EvaluationResults.EvaluatorError(msg) => Right(msg)
      case EvaluationResults.RuntimeError(msg) => Right(msg)
      case m => Right("An error occurred. Sorry not to be able to give more information than " + m)
    } } catch {
      case e: Exception => Right("An exception was thrown: " + e)
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

  def weakCondition(v: Variable, c: OriginalValue): Exp = E(perfect.Utils.original)(v === c.e)

  val replaceNewLines = postMap {
    case StringLiteral(n) => Some(StringLiteral(n.replaceAllLiterally("\n", "@LF#!")))
    case _ => None
  } _
  val reinsertNewLines = postMap {
    case StringLiteral(n) => Some(StringLiteral(n.replaceAllLiterally("@LF#!", "\n")))
    case _ => None
  } _

  def solveGeneralConstraints(constraint: Exp, freeVariables: Seq[Var]): Stream[Map[Var, Exp]] = {
    val input = Variable(FreshIdentifier("input"), tupleTypeWrap(freeVariables.map(_.getType)), Set())
    val fullconstraint = InoxConstraint(replaceNewLines(input === tupleWrap(freeVariables) &<>& constraint))
    Log(s"Solving as $fullconstraint")
    fullconstraint.toStreamOfInoxExpr(input).map(reinsertNewLines).map {
      case Tuple(args) => freeVariables.zip(args).map{ case (fv: Var, expr: Exp) => fv -> expr }.toMap
      case e if freeVariables.length == 1 => Map(freeVariables.head -> e)
      case UnitLiteral() if freeVariables.length == 0 => Map[Var, Exp]()
      case e =>
        throw new Exception(s"Other unexpected solution: $e")
    }
  }



  /** Obtain all possible assignments from the formula Cont for the given free variables */

  // Members declared in perfect.core.ProgramUpdater
  def Assign(v: Variable, e: Expr, body: Expr): Expr = inox.trees.Let(v.toVal, e, body)
  def isValue(e: Expr): Boolean = perfect.Utils.isValue(e)
  def isVar(e: Expr): Boolean = e.isInstanceOf[Variable]

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
  def extractLambda(e: Exp): Option[(Seq[Var], Exp)] = e match {
    case inox.trees.Lambda(vds, body) => Some((vds.map(_.toVariable), body))
    case _ => None
  }

  // Members declared in perfect.core.predef.LetLenses
  def buildLet(v: Var,assigned: Exp,body: Exp): Exp = inox.trees.Let(v.toVal, assigned, body)
  def extractLet(e: Exp): Option[(Var, Exp, Exp)] = e match {
    case inox.trees.Let(v, thn, elz) => Some((v.toVariable, thn, elz))
    case _ => None
  }

  // Members declared in perfect.core.FunctionInvocationLenses
  def extractInvocation(e: Exp)(implicit symbols: Symbols, cache: Cache): Option[(Seq[Exp], Seq[Exp] => Exp)] = e match {
    case inox.trees.FunctionInvocation(id, tpe, args) => Some((args, newArgs => inox.trees.FunctionInvocation(id, tpe, newArgs)))
    case _ => None
  }

  // Members declared in perfect.core.predef.ListLenses
  def extractList(e: Exp): Option[(List[Exp], List[Exp] => Exp)] = e match {
    case perfect.ListLiteral(elements, builder) => Some((elements, builder))
    case _ => None
  }

  def freshVar(exp: Exp, name: Option[String], showUniqueId: Boolean, others: Var*)(implicit symbols: Symbols): Var = {
    val n = name.getOrElse(exp match {
      case Variable(id, _, _) => id.name
      case _ => Utils.makeVariableName(exp.toString)
    })
    val nWithoutConflicts = Utils.uniqueName(n, others.map(_.id.name).toSet)
    Variable(FreshIdentifier(nWithoutConflicts , showUniqueId), exp.getType, Set())
  }

  /** Returns the default value of the unique argument of the lambda, */
  def extractLambdaDefaultArgument(e: Exp): Option[Exp] = e match {
    case inox.trees.Lambda(Seq(vd), body) => Some(perfect.Utils.defaultValue(vd.tpe))
    case _ => None
  }
  /** Returns an "unknown" fresh variable matching the type of the lambda's first argument*/
  def extractLambdaUnknownVar(e: Exp): Option[Var] = e match {
    case inox.trees.Lambda(vd +: _, body) => Some(Variable(FreshIdentifier("unknown", true), vd.tpe, Set()))
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

  def buildListInsertGoal(before: List[Exp], inserted: List[Exp], after: List[Exp], direction: AssociativeInsert.InsertDirection)(implicit symbols: Symbols): Exp = {
    val t = (before ++ inserted ++ after).headOption.map(_.getType)
    ListInsertGoal(t.getOrElse(throw new Exception("Empty list insert goals not supported")), before, inserted, after/*, direction*/)
  }


  def mkStringVar(name: String, avoid: Var*): Var = {
    Variable(FreshIdentifier(perfect.Utils.uniqueName(name, avoid.map(_.id.name).toSet)), StringType, Set())
  }
  def mkStringVar(original: Var, avoid: Var*): Var = {
    mkStringVar(original.id.name, avoid: _*)
  }

  def isSameInvocation(e: Expr, g: Expr)(implicit symbols: Symbols, cache: Cache) = e match {
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
    case inox.trees.ADT(tpe, args) => Some((args, x => inox.trees.ADT(tpe, x)))
    case _ => None
  }

  var xCounter = 1
  def extractADTSelector(e: Exp)(implicit symbols: Symbols): Option[(Exp, Exp => Exp, Exp => Seq[Var], Int)]  = e match {
    case as@inox.trees.ADTSelector(expr, id) =>
      val index = as.selectorIndex

      val vrsBuilder = (x: Exp) => x match {
        case ADT(adt, args) =>
          val constructor = adt.lookupADT.get.toConstructor
          val fields = constructor.fields
          val vrs = fields.map { fd => Variable(FreshIdentifier("x"+{ xCounter += 1; xCounter }, false), fd.getType, Set()) }
          vrs
      }
      Some((expr, x => inox.trees.ADTSelector(x, id), vrsBuilder, index))
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
      Option[(Exp, Int)] = goal match {
    case TreeModificationGoal(lambda, modified, index) => Some((modified, index))
    case _ => None
  }

  /** Returns a goal with the original tree, the modified tree, and the next path element.
    * The second exp of the path element should continue with TreeMdodificationGoal until the modified
    * part of the original is reached. */
  def buildTreeModificationGoal(original: Exp, modified: Exp, index: Int)(implicit symbols: Symbols): Exp = {
    perfect.semanticlenses.TreeModificationGoal(original, modified, index)
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
  def buildPasteStringVarGoal(left: String,v: Var,v_value: String,right: String,direction: InsertDirection): Exp = {
    PasteVariableGoal(left, v, v_value, right, direction)
  }
  def extractPasteStringVarGoal(e: Exp): Option[(String, Var, String, String, InsertDirection)] = {
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
  def extractStringConcat(e: Exp): Option[(Exp, Exp)] = e match {
    case inox.trees.StringConcat(a, b) => Some((a, b))
    case _ => None
  }

  // Members declared in perfect.lenses.StringInsertLenses
  def buildStringInsertGoal(left: String,inserted: String,right: String,direction: perfect.InoxProgramUpdater.AssociativeInsert.InsertDirection): Exp = {
    StringInsertGoal(left, inserted, right, direction)
  }
  def extractStringInsertGoal(e: Exp): Option[(String, String, String, perfect.InoxProgramUpdater.AssociativeInsert.InsertDirection)] = {
    StringInsertGoal.unapply(e)
  }

  // Members declared in perfect.core.predef.StringLenses
  def buildStringLiteral(e: String): Exp = inox.trees.StringLiteral(e)
  def extractStringliteral(e: Exp): Option[String] = e match {
    case inox.trees.StringLiteral(s) => Some(s)
    case _ => None
  }
  
  // Members declared in perfect.core.predef.ListConcatLenses
  def buildListConcat(left: Exp,right: Exp)(implicit symbols: Symbols): Exp = {
    left.getType match {
      case ADTType(_, Seq(tp)) => E(perfect.Utils.listconcat)(tp)(left, right)
      case _ => throw new Exception(s"Could not figure out type of $left")
    }
  }
  def extractListConcat(e: Exp): Option[(Exp, Exp, (Exp, Exp) => Exp)] = e match {
    case FunctionInvocation(perfect.Utils.listconcat, tp, Seq(left, right)) =>
      Some((left, right, (left, right) => FunctionInvocation(perfect.Utils.listconcat, tp, Seq(left, right))))
    case _ => None
  }

  // Lenses which do not need the value of the program to invert it.
  val shapeLenses: SemanticLens =
    combine(ShortcutGoal(
      Map(TreeWrapGoal.id -> TreeWrapLens,
      TreeUnwrapGoal.id -> TreeUnwrapLens,
      TreeModificationGoal.id -> TreeModificationLens.named("tree modification")),
      (x: Exp) => x match { case FunctionInvocation(id, _, _) => Some(id) case _ => None } ),
    ValueLens)

  def functionInvocationLens: SemanticLens =
    ShortcutLens(Map[inox.Identifier, SemanticLens](
      perfect.Utils.filter -> FilterLens,
      perfect.Utils.map -> MapLens.named("Map Lens"),
      perfect.Utils.mkString -> MkStringLens,
      perfect.Utils.rec2 -> RecursiveLens,
      perfect.Utils.dummyStringConcat -> StringConcatLens,
      perfect.Utils.listconcat -> ListConcatLens,
      perfect.Utils.flatmap -> FlatMapLens,
      perfect.Utils.sortWith -> SortWithLens
      // TODO: Add all lenses from lenses.Lenses
      /*
      FlattenLens,*/
    ), {
      case FunctionInvocation(id, _, _) => Some(id)
      case StringConcat(_, _) => Some(perfect.Utils.dummyStringConcat)
      case e => None
    }).named("Dispatch function invocation")
  import perfect.lenses._

// Lenses which need the value of the program to invert it.
  val semanticLenses: SemanticLens = valueLenses // andThen

  override def debug = true //Log.activate

  val lens = combine(
    NoChangeLens.named("No Change?"),
    ConstantReplaceLens.named("ConstantReplace"),
    shapeLenses.named("Shape?"),
    WrapperLens(semanticLenses.named("Semantic?") andThen defaultLens.named("default"), WrappedADTLens.named("wrapped ADT") andThen WrappedStringLens)
    , FinalLens.named(s"/!\\ Warning could not transform")
  )
}


