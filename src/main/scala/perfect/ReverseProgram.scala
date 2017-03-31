package perfect

import inox.Identifier
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
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

  object ProgramFormula {
    import inox.trees.dsl._
    // Contains the original value of the program to repair.
    val tree = FreshIdentifier("tree") // Serves as a placeholder to identify where the tree was inserted.
    
    // For semantic unwrap
    val subtree = FreshIdentifier("subtree")
    
    // For semantic insert for string
    // ProgramFormula(leftTreeStr +& "The Insertion" +& rightTreeStr,
    //   tree == leftTreeStr +& rightTreeStr && leftTreeStr == "String to the left && rightTreeStr = "String to the right"

    def apply(e: Expr, f: Expr): ProgramFormula = ProgramFormula(e, Formula(f))

    /** To build and extract a StringInsert specification. Works for modifications as well */
    object StringInsert {
      private val leftName = "leftTreeStr"
      private val rightName = "rightTreeStr"

      def apply(left: Expr, s: Expr, right: Expr): ProgramFormula = {
         val leftTreeStr = Variable(FreshIdentifier(leftName, true), StringType, Set())
        val rightTreeStr = Variable(FreshIdentifier(rightName, true), StringType, Set())
        ProgramFormula(
          leftTreeStr +& s +& rightTreeStr,
          // tree === leftTreeStr +& rightTreeStr && (if not modificaiton)
          leftTreeStr === left && rightTreeStr === right
        )
      }

      def unapply(f: ProgramFormula): Option[(String, String, String)] = {
        f.expr match {
          case (leftTreeStr@Variable(idLeft, StringType, _)) +& StringLiteral(inserted) +& (rightTreeStr@Variable(idRight, StringType, _))
            if idLeft.name == leftName && idRight.name == rightName
          =>
            val StringLiteral(leftBefore) = f.formula.known(leftTreeStr.toVal)
            val StringLiteral(rightBefore) = f.formula.known(rightTreeStr.toVal)
            Some((leftBefore, inserted, rightBefore))
          case _ => None
        }
      }
    }

    /** To build and extract a StringDelete specification */
    object StringDelete {
      private val leftName = "leftTreeStr"
      private val rightName = "rightTreeStr"
      def apply(left: Expr, right: Expr): ProgramFormula = {
        val leftTreeStr = Variable(FreshIdentifier(leftName, true), StringType, Set())
        val rightTreeStr = Variable(FreshIdentifier(rightName, true), StringType, Set())
        ProgramFormula(
          leftTreeStr +& rightTreeStr,
          leftTreeStr === left && rightTreeStr === right
        )
      }

      def unapply(f: ProgramFormula): Option[(String, String)] = {
        f.expr match {
          case (leftTreeStr@Variable(idLeft, StringType, _)) +& (rightTreeStr@Variable(idRight, StringType, _))
            if idLeft.name == leftName && idRight.name == rightName
          =>
            val StringLiteral(leftBefore) = f.formula.known(leftTreeStr.toVal)
            val StringLiteral(rightBefore) = f.formula.known(rightTreeStr.toVal)
            Some((leftBefore, rightBefore))
          case _ => None
        }
      }
    }

    // Used to extract clone and paste expressions, when paste is to the right of the clone.
    object CloneAndPasteRight {
      val cloneName = "clone"
      val pasteName = "paste"

      def apply(beforeCloneValue: Expr, cloneValue: Expr, betweenClonePasteValue: Expr, afterPasteValue: Expr): ProgramFormula = {
        val clone = Variable(FreshIdentifier(cloneName, true), StringType, Set())
        val paste = Variable(FreshIdentifier(pasteName, true), StringType, Set())

        ProgramFormula(
          beforeCloneValue +& clone +& betweenClonePasteValue +& paste +& afterPasteValue,
          clone === cloneValue && paste === clone
        )
      }

      def unapply(pf: ProgramFormula): Option[(String, String, String, String)] = {
        pf.expr match {
          case StringLiteral(bcvalue) +& (clone@Variable(id, _, _)) +& StringLiteral(bcpvalue) +& (paste@Variable(id2, _, _)) +& StringLiteral(apvalue)
            if id.name == cloneName && id2.name == pasteName =>
            val StringLiteral(cloneValue) = pf.formula.known(clone.toVal)
            Some((bcvalue, cloneValue, bcpvalue, apvalue))
          case _ => None
        }
      }
    }

    // Used to extract clone and paste expressions, when paste is to the left of the clone.
    object CloneAndPasteLeft {
      val cloneName = "clone"
      val pasteName = "paste"

      def apply(beforePasteValue: Expr, betweenPasteCloneValue: Expr, cloneValue: Expr, afterCloneValue: Expr): ProgramFormula = {
        val clone = Variable(FreshIdentifier(cloneName, true), StringType, Set())
        val paste = Variable(FreshIdentifier(pasteName, true), StringType, Set())

        ProgramFormula(
          beforePasteValue +& paste +& betweenPasteCloneValue +& clone +& afterCloneValue,
          clone === cloneValue && paste === clone
        )
      }

      def unapply(pf: ProgramFormula): Option[(String, String, String, String)] = {
        pf.expr match {
          case StringLiteral(bpvalue) +& (paste@Variable(id2, _, _)) +& StringLiteral(bpcvalue) +& (clone@Variable(id, _, _)) +& StringLiteral(acvalue)
            if id.name == cloneName && id2.name == pasteName =>
            val StringLiteral(cloneValue) = pf.formula.known(clone.toVal)
            Some((bpvalue, bpcvalue, cloneValue, acvalue))
          case _ => None
        }
      }
    }
  }

  case class ProgramFormula(expr: Expr, formula: Formula = Formula()) {
    lazy val freeVars: Set[ValDef] = exprOps.variablesOf(expr).map(_.toVal)
    lazy val unchanged: Set[ValDef] = freeVars -- formula.varsToAssign

    override def toString = expr.toString + s" [$formula]" + (if(canDoWrapping) " (wrapping enabled)" else "")
    var canDoWrapping = false

    def wrappingEnabled: this.type = {
      this.canDoWrapping = true
      this
    }

    def withComputedValue(e: Expr): this.type = {
      givenValue = Some(e)
      this
    }

    // Can be set-up externally to bypass the computation of the function value.
    // Must be set before a call to functionValue using .withComputedValue
    private var givenValue: Option[Expr] = None

    lazy val bodyDefinition: Option[Expr] = formula.assignments.map(f => f(expr))

    def getFunctionValue(implicit cache: Cache, symbols: Symbols): Option[Expr] = {
      givenValue match {
        case Some(e) => givenValue
        case None => formula.assignments match {
          case Some(f) =>
            val res = evalWithCache(f(expr))
            givenValue = Some(res)
            givenValue
          case _ => None
        }
      }
    }

    def functionValue(implicit cache: Cache, symbols: Symbols): Expr = {
      givenValue match {
        case Some(e) => e
        case None =>
          val res =
          if((freeVars -- formula.known.keySet).isEmpty) {
            evalWithCache(letm(formula.known) in expr)
          } else {
            throw new Exception(s"[Internal error] Tried to compute a function value but not all variables were known (only ${formula.known.keySet} are).\n$this")
          }
          givenValue = Some(res)
          res
      }
    }

    /** Uses the result of a programFormula by wrapping the expression */
    def wrap(f: Expr => Expr): ProgramFormula = {
      val newProgram = f(expr)
      ProgramFormula(newProgram, formula)
    }

    /** Replaces the expression with another, for defining sub-problems mostly. */
    def subExpr(f: Expr): ProgramFormula = {
      ProgramFormula(f, formula)
    }

    def withoutConstraints(): ProgramFormula = {
      ProgramFormula(expr)
    }

    /** Augment this expr with the given formula */
    def combineWith(f: Formula): ProgramFormula = {
      ProgramFormula(expr, formula combineWith f)
    }
  }

  object Formula {
    /** A deterministic constructor for Formula */
    def apply(known: Map[ValDef, Expr]): Formula = {
      val f = Formula(and(known.toSeq.map(x => x._1.toVariable === x._2): _*))
      f.givenKnown = Some(known)
      f
    }
  }

  case class Formula(unknownConstraints: Expr = BooleanLiteral(true)) { // Can contain middle free variables.
    lazy val varsToAssign = known.keySet ++ (exprOps.variablesOf(unknownConstraints).map(_.toVal))

    //val TopLevelAnds(ands) = unknownConstraints
    //assert(ands.forall(x => !x.isInstanceOf[Lambda]))

    private var givenKnown: Option[Map[ValDef, Expr]] = None

    lazy val known: Map[ValDef, Expr] = givenKnown.getOrElse{
      val TopLevelAnds(ands) = unknownConstraints
      ands.flatMap {
        case Equals(v: Variable, e: Expr) if(isValue(e)) => // TODO: Try to remove "isValue"
          List(v.toVal -> e)
        case _ => Nil
      }.toMap
    }

    /** If the constraints are complete, i.e. all variables can be defined, then we can generate a let-wrapper. */
    lazy val assignments: Option[Expr => Expr] = {
      def rec(constraints: List[Expr], seen: Set[Variable]): Option[Expr => Expr] = {
        if(constraints == Nil) Some(x => x) else {
          constraints.collectFirst[(Expr => Expr, Variable, Equals)]{
            case equ@Equals(v: Variable, e: Expr) if (exprOps.variablesOf(e) -- seen).isEmpty =>
              ((x: Expr) => Let(v.toVal, e, x), v, equ)
            case equ@Equals(e: Expr, v: Variable) if (exprOps.variablesOf(e) -- seen).isEmpty =>
              ((x: Expr) => Let(v.toVal, e, x), v, equ)
          }.flatMap{ fve => rec(constraints.filter(x => x != fve._3), seen + fve._2).map(
              (g: Expr => Expr) => ((x: Expr) => fve._1(g(x))))
          }
        }
      }
      val TopLevelAnds(ands) = unknownConstraints
      rec(ands.toList.filter(x => x != BooleanLiteral(true)), Set())
    }

    def combineWith(other: Formula): Formula = {
      Formula(unknownConstraints &<>& other.unknownConstraints)
    }

    override def toString = "[" + unknownConstraints.toString() + "]"
    private lazy val unknownConstraintsVars: Set[ValDef] = exprOps.variablesOf(unknownConstraints).map(_.toVal)

    /** Returns an expression equal to the value of vd*/
    def getOrElse(vd: ValDef, e: =>Expr): Expr = {
      known.getOrElse(vd, {
        if(varsToAssign(vd)) {
          vd.toVariable
        } else e // The expression is unchanged, we return the original expression
      })
    }

    /** Finds the 'value' of a variable in the lhs of a constraint*/
    def findConstraintValue(v: Variable): Option[Expr] = {
      unknownConstraints match {
        case TopLevelAnds(ands) =>
          ands.collectFirst[Expr] {
            case Equals(mapVar, value)
              if mapVar == v => value
          }.orElse{
            ands.collectFirst[Expr] {
              case FunctionInvocation(Utils.maybe, _, Seq(
              Equals(mapVar, value))) if mapVar == v => value
            }
          }
        case _ => None
      }
    }

    /** Finds the value of an element in a map, in the formula */
    def findConstraintVariableOrLiteral(m: MapApply): Expr = m match {
      case MapApply(v: Variable, key) =>
        findConstraintValue(v) match {
          case Some(FiniteMap(pairs, _, _, _)) =>
            pairs.find(_._1 == key).map(_._2).getOrElse{
              throw new Exception(s"Could not find key/value $v -> $key in "+unknownConstraints)
            }
          case _ =>
            throw new Exception(s"Could not find key/value $v -> $key in "+unknownConstraints)
        }
      case MapApply(v: MapApply, k) =>
        findConstraintVariableOrLiteral(MapApply(findConstraintVariableOrLiteral(v), k))
      case _ => throw new Exception(s"Not a well formed MapApply: $m")
    }

    // The assignments and the formula containing the other expressions.
    def determinizeAll(freeVariables: Seq[ValDef] = varsToAssign.toSeq)(implicit symbols: Symbols): Stream[Map[ValDef, Expr]] = {

      Log(s"Trying to get all solutions for $varsToAssign of \n" + this)
      //val freeVariables = varsToAssign.toSeq

      unknownConstraints match {
        case BooleanLiteral(true) => Stream(freeVariables.map(fv => fv -> known(fv)).toMap)
        case BooleanLiteral(false) => Stream.empty
        case _ =>
          val input = Variable(FreshIdentifier("input"), tupleTypeWrap(freeVariables.map(_.getType)), Set())
          //println(s"input is of type ${input.getType}")
          val constraint = InoxConstraint(input === tupleWrap(freeVariables.map(_.toVariable)) && unknownConstraints && and(known.toSeq.map{ case (k, v) => k.toVariable === v} : _*))
          Log(s"Solving for $constraint")
          constraint.toStreamOfInoxExpr(input).map {
            case Tuple(args) => freeVariables.zip(args).map{ case (fv: ValDef, expr: Expr) => fv -> expr }.toMap
            case e if freeVariables.length == 1 =>
              Map(freeVariables.head -> e)
            case e =>
              Log("other solution : " + e)
              Map[ValDef, Expr]()
          }
      }
    }

    /* Force the evaluation of the constraints to evaluate an expression*/
    def evalPossible(e: Expr)(implicit cache: Cache, symbols: Symbols): Stream[Expr] = {
      for(assignment <- determinizeAll()) yield {
        evalWithCache(letm(known ++ assignment) in e)
      }
    }
  }

  import Utils._
  import InoxConvertible._
  lazy val context = Context.empty.copy(options = Options(Seq(optSelectedSolvers(Set("smt-cvc4")))))

  /** Automatic simplification of EXPR1 && EXPR2 if one is true.*/
  implicit class BooleanSimplification(f: Expr) {
    @inline def &<>&(other: Expr): Expr = other match {
      case BooleanLiteral(true) => f
      case BooleanLiteral(false) => other
      case _ => f match {
        case BooleanLiteral(true) => other
        case BooleanLiteral(false) => f
        case _ => f && other
      }
    }
  }

  /** Returns the stream b if a is empty, else only a. */
  def ifEmpty[A](a: Stream[A])(b: =>Stream[A]): Stream[A] = {
    if(a.isEmpty) b else a
  }

  /*def put[A: InoxConvertible](out: A, prevIn: Option[(InoxProgram, FunctionEntry)]): Iterable[(InoxProgram, FunctionEntry)] = {
    put(inoxExprOf[A](out), prevIn)
  }*/

  def put(outProg: ProgramFormula, prevIn: Option[Expr]): Stream[Expr] = {
    if(prevIn == None) {
      val outExpr = outProg.bodyDefinition.getOrElse(throw new Exception(s"Ill-formed program: $outProg"))
      return Stream(outExpr)
    }
    implicit val symbols = defaultSymbols.withFunctions(ReverseProgram.funDefs)
    implicit val cache = new HashMap[Expr, Expr]
    val newMain = FreshIdentifier("main")
    for { r <- repair(ProgramFormula(prevIn.get), outProg)
          ProgramFormula(newOutExpr, f) = r
          _ = Log("Remaining formula: " + f)
          _ = Log("Remaining expression: " + newOutExpr)
          assignments <- f.determinizeAll(exprOps.variablesOf(newOutExpr).toSeq.map(_.toVal))
          _ = Log("Found assignments: " + assignments)
          finalNewOutExpr = exprOps.replaceFromSymbols(assignments, newOutExpr)
          _ = Log("Final  expression: " + finalNewOutExpr)
    } yield finalNewOutExpr
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

  /** Eval function. Uses a cache normally*/
  def evalWithCache(expr: Expr)(implicit cache: Cache, symbols: Symbols) = cache.getOrElseUpdate(expr, {
    import evaluators._
    val funDef = mkFunDef(FreshIdentifier("main"))()(stp => (Seq(), expr.getType, _ => expr))
    val p = InoxProgram(context, symbols)
    val evaluator = LambdaPreservingEvaluator(p)
    evaluator.eval(expr) match {
      case EvaluationResults.Successful(e) => e
      case m => throw new Exception(s"Could not evaluate: $expr, got $m")
    }
  })

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

  private case class letm(v: Map[ValDef, Expr]) {
    @inline def in(res: Expr) = {
      (res /: v) {
        case (res, (key, value)) => let(key, value)(_ => res)
      }
    }
  }

  /** Match lambda's bodies to recover the original assignments */
  def obtainMapping(originalInput: Expr, freeVars: Set[Variable], originalAssignments: Map[ValDef, Expr], output: Expr): Stream[Map[ValDef, Expr]] = {
    //Log.prefix(s"obtainMapping($originalInput, $freeVars, $originalAssignments, $output) =") :=
    (originalInput, output) match {
      case (v: Variable, l) =>
        if(freeVars(v)) {
          //Log(s"$v is a free variable")
          if(!(originalAssignments contains v.toVal) || l == originalAssignments(v.toVal)) {
            //Log(s"Value unchanged")
            Stream(Map())
          } else {
            //Log(s"Value updated: $l")
            Stream(Map(v.toVal -> l))
          }
        } else Stream(Map())
      case (Operator(subtrees, _), Operator(subtrees2, _)) =>
        if(subtrees.length == subtrees2.length) {
          inox.utils.StreamUtils.cartesianProduct(
            subtrees.zip(subtrees2).map{ case (a, b) => obtainMapping(a, freeVars, originalAssignments, b)}
          ).flatMap{ (e: Seq[Map[ValDef, Expr]]) =>
            def combineAll(remaining: Seq[Map[ValDef, Expr]], current: Map[ValDef, Expr]): Stream[Map[ValDef, Expr]] = {
              //Log(s"combineAll($remaining, $current)")
              remaining match {
              case Seq() =>
                //Log(s"returning $current")
                Stream(current)
              case head +: tail =>
                val intersection = inox.utils.StreamUtils.cartesianProduct(
                  (current.keySet intersect head.keySet).toSeq.map{ key =>
                    if(current(key) != head(key)) {
                      Stream(key -> current(key), key -> head(key))
                    } else {
                      Stream(key -> current(key))
                    }
                  } ++ (head.keySet -- current.keys).map{ key => Stream(key -> head(key))}
                ).map{ _.toMap }
                //Log(s"intersection = $intersection")
                if(intersection.nonEmpty) {
                  // We get all variants from the intersection
                  intersection.flatMap{ possiblity => combineAll(tail, current ++ possiblity )}
                } else combineAll(tail, current ++ head)
              }
            }
            combineAll(e, Map())
          }
        } else Stream.empty
    }
  }

  /** Applies the interleaving to a finite sequence of streams. */
  def interleave[T](left: Stream[T])(right: => Stream[T]) : Stream[T] = {
    if (left.isEmpty) right else left.head #:: interleave(right)(left.tail)
  }

  /** Will try its best to transform prevOutExpr so that it produces newOut or at least incorporates the changes.
    * Basically, we solve the problem:
    *  let variables = values in function = newOut
    * by trying to change the variables values, or the function body itself.
    *
    * @param program An expression that computed the value before newOut, and the formula contains the current mappings.
    * @param newOut A ProgramFormula resulting from the action of the user on the datat.
    *               Either a literal value that should be produced by function,
    *               or a variable, in which case the result will have in the formula a constraint over this variable,
    *               Or an expression with constrained free variables to denote a clone-and-paste or many other things.
    * @return A set of possible expressions, along with a set of possible assignments to input variables.
    **/
  def repair(program: ProgramFormula, newOutProgram: ProgramFormula)
            (implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    val ProgramFormula(function, functionformula) = program
    val ProgramFormula(newOut, newOutFormula) = newOutProgram
    val currentValues = functionformula.known
    val stackLevel = Thread.currentThread().getStackTrace.length
    Log(s"\n@repair$stackLevel(\n  $program\n, $newOutProgram)")
    if(function == newOut) return { Log("@return original without constraints");
      Stream(program.withoutConstraints())
    }

    val treeVar = Variable(ProgramFormula.tree, program.expr.getType, Set())
    if(!function.isInstanceOf[Let] && program.canDoWrapping &&
      newOutFormula.unknownConstraints != BooleanLiteral(true) &&
      (exprOps.variablesOf(newOut) contains treeVar)) { // Maybe there is just a wrapping

      newOutFormula.findConstraintValue(treeVar) match {
        case Some(treeValue) => if(isValue(treeValue)) {
          Log("@return wrapped around tree: " + newOutProgram);
          return Stream(ProgramFormula(exprOps.replaceFromSymbols(Map(ValDef(ProgramFormula.tree, program.expr.getType, Set()) ->
            function
          ), newOut)))
        } else {
          //treeValue is not a simple value, there is some splitting to do to determine the value of the free variables.

          if(exprOps.variablesOf(treeValue).map(_.id) == Set(ProgramFormula.subtree)) {
            for{ pf <- repair(program, ProgramFormula(treeValue, newOutFormula)) } yield {
              // This gives a solution assignment for subtree as well as variables on the rhs.
              ???
            }
          }
        }
        case None =>
      }
    }

    lazy val functionValue = program.functionValue

    if(!newOut.isInstanceOf[Variable] && functionValue == newOut) return {
      Log("@return original function");
      Stream(program.withoutConstraints())
    }

    //Log.prefix(s"@return ") :=
    interleave {
      function.getType match {
        case a: ADTType if !newOut.isInstanceOf[Variable] =>
          function match {
            case l: Let => Stream.empty[ProgramFormula] // No need to wrap a let expression, we can always do this later. Indeed,
              //f{val x = A; B} = {val x = A; f(B)}
            case Application(Lambda(_, _), _) => Stream.empty[ProgramFormula] // Same argument
            case _ =>
              maybeWrap(program, newOut, functionValue) #::: maybeUnwrap(program, newOut, functionValue)
          }
        case StringType if !newOut.isInstanceOf[Variable] && program.canDoWrapping =>
          function match {
            case l: Let => Stream.empty[ProgramFormula]
            case Application(Lambda(_, _), _) => Stream.empty[ProgramFormula]
            case _ =>
              // Stream.empty
              // Can be a StringConcat with constants to add or to remove.
              maybeWrapString(program, newOut, functionValue)// #::: maybeUnwrapString(program, newOut, functionValue)
          }
        case _ => Stream.empty[ProgramFormula]
      }
    } {
      function match {
        // Values (including lambdas) should be immediately replaced by the new value
        case l: Literal[_] =>
          newOut match {
            case v: Variable => // Replacement with the variable newOut, with a maybe clause.
              Stream(ProgramFormula(newOut))
            case l: Literal[_] => // Raw replacement
              Stream(ProgramFormula(newOut))
            case m: MapApply =>
              repair(program, newOutProgram.subExpr(program.formula.findConstraintVariableOrLiteral(m)))

            /*case l@Let(cloned: ValDef, _, _) =>
              Stream(ProgramFormula(newOut, Formula(Map(), Set(), Set(), BooleanLiteral(true))))*/
            case _ =>
              newOutProgram match {
                case ProgramFormula.StringInsert(left, inserted, right) =>
                  Stream(ProgramFormula(StringLiteral(left + inserted + right)))
                case ProgramFormula.StringDelete(left, right) =>
                  Stream(ProgramFormula(StringLiteral(left + right)))
                case _ =>
                  throw new Exception("Don't know what to do, not a Literal, a Variable, a let, a string insertion or deletion: "+newOut)
              }
          }
        case l: FiniteSet =>
          if(isValue(l) && newOut.isInstanceOf[FiniteSet]) {
            val fs = newOut.asInstanceOf[FiniteSet]
            Stream(ProgramFormula(newOut))
          } else {
            lazy val evaledElements = l.elements.map{ e =>
              (evalWithCache(letm(currentValues) in e), e)}
            newOut match {
              case fs: FiniteSet =>
                // Since there is no order, there is no point repairing expressions,
                // only adding new ones and deleting old ones.
                val expectedElements = fs.elements.toSet
                val newElements = evaledElements.filter{
                  case (v, e) => expectedElements contains v
                }.map(_._2) ++ expectedElements.filter(x =>
                  !evaledElements.exists(_._1 == x))
                Stream(ProgramFormula(FiniteSet(newElements, fs.base)))
              case newOut => // Maybe it has a formula ?
                val insertedElements = newOut match {
                  case v: Variable => program.formula.findConstraintValue(v) match {
                    case Some(fs: FiniteSet) =>
                      fs.elements.filter{ e =>
                        !evaledElements.exists(_._1 == e)
                      }
                    case _ => Nil
                  }
                  case _ => Nil
                }
                Stream(ProgramFormula(
                  FiniteSet(l.elements ++ insertedElements, l.base)))
            }
          }
        case l: FiniteMap =>
          if(isValue(l) && newOut.isInstanceOf[FiniteMap]) {
            newOut match {
              /*case v: Variable => // Replacement with the variable newOut, with a maybe clause.
                // We loose the variable order !
                val maybes = and(l.pairs.map {
                  case (key_v, value_v) => E(Utils.maybe)(MapApply(newOut, key_v) === value_v)
                }: _*)

                Stream(ProgramFormula(newOut, Formula(unknownConstraints=maybes)))
              */case fm: FiniteMap => // Raw replacement
                Stream(ProgramFormula(newOut))
              /*case l@Let(cloned: ValDef, _, _) =>
              Stream(ProgramFormula(newOut, Formula(Map(), Set(), Set(), BooleanLiteral(true))))*/
              case _ => throw new Exception("Don't know what to do, not a Literal or a Variable " + newOut)
            }
          } else {
            // Check for changed keys, removals and additions.
            lazy val partEvaledPairs = l.pairs.map{ case (key, value) =>
              (evalWithCache(letm(currentValues) in key), (key, value, evalWithCache(letm(currentValues) in value)))
            }
            newOut match {
              case fm: FiniteMap => // Raw replacement
                val (newFiniteMapKV) = (ListBuffer[Stream[(Expr, ProgramFormula)]]() /: partEvaledPairs) {
                  case (lb, (key_v, (key, value, value_v))) =>
                    if(!fm.pairs.exists(_._1 == key_v)) {
                      lb
                    } else {
                      val i = fm.pairs.lastIndexWhere(_._1 == key_v)
                      val newValue = fm.pairs(i)._2
                      lb += repair(program.subExpr(value), newOutProgram.subExpr(newValue)).map(pf => (key, pf))
                    }
                }.toList
                for {solution <- inox.utils.StreamUtils.cartesianProduct(newFiniteMapKV)
                     (mapKeys, mapValuesFormula) = solution.unzip
                     mapValues = mapValuesFormula.map(_.expr)
                     mapFormula = mapValuesFormula.map(_.formula)
                     formula = (Formula() /: mapFormula){ case (f, ff) => f combineWith ff }
                } yield {
                  ProgramFormula(FiniteMap(mapKeys.zip(mapValues), l.default, l.keyType, l.valueType), formula)
                }
              case newOut =>
                val insertedPairs = newOut match {
                  case v: Variable => program.formula.findConstraintValue(v) match {
                    case Some(np: FiniteMap) => np.pairs.filter {
                      case (k, v) => !partEvaledPairs.exists(x => x._1 == k)
                    }
                    case _ => Nil
                  }
                  case _ => Nil
                }
                // We output the constraints with the given FiniteMap description.
                // We repair symbolically on every map's value.
                val repairs = partEvaledPairs.map{
                  case (key_v, (key, value, value_v)) =>
                    repair(program.subExpr(value), newOutProgram.subExpr(MapApply(newOut, key))).map((key_v, _))
                }
                for{keys_pf_seq <- inox.utils.StreamUtils.cartesianProduct(repairs)} yield {
                  val (keys, pf_seq) = keys_pf_seq.unzip
                  val (list_m, formula) = combineResults(pf_seq, currentValues)
                  val new_exprs = keys.zip(list_m).toMap
                  // Keep the original order.
                  val newPairs = (partEvaledPairs map {
                    case (key_v, (key, value, value_v)) => key -> new_exprs(key_v)
                  }) ++ insertedPairs
                  ProgramFormula(
                    FiniteMap(newPairs, l.default, l.keyType, l.valueType),
                    formula)
                }
              //case _ => throw new Exception("Don't know what to do, not a Literal or a Variable: " + newOut)
            }

          }
        case lFun@Lambda(vd, body) =>  // Check for closures, i.e. free variables.
          val freeVars = exprOps.variablesOf(body).map(_.toVal) -- vd
          if(freeVars.isEmpty) {
            newOut match {
              case l: Lambda =>
                val freeVarsOfOut = exprOps.variablesOf(l)

                if(freeVarsOfOut.isEmpty) {
                  Stream(ProgramFormula(newOut))
                } else
                for {maybeMapping <- obtainMapping(l, freeVarsOfOut, Map(), lFun)
                     constraint = and(maybeMapping.toSeq.map { case (k, v) => E(Utils.maybe)(k.toVariable === v) }: _*) /: Log.constraint
                } yield {
                  Log("Returning formula")
                  ProgramFormula(newOut, Formula(unknownConstraints=constraint))
                }
              case v: Variable =>
                Stream(ProgramFormula(newOut))
              case _ => ???
            }
          }  else { // Closure
            if(exprOps.variablesOf(newOut) == freeVars) { // Same free variables, we just take the new out.
              Stream(ProgramFormula(newOut))
            } else
            // We need to determine the values of these free variables. We assume that the lambda kept the same shape.
            newOut match {
            case Lambda(vd2, expectedBody) =>
              val oldToFresh = vd.map{ v =>
                v -> ValDef(FreshIdentifier(v.id.name, true), v.tpe, v.flags)
              }.toMap
              val freshToOld = oldToFresh.map{ case (k, v) => v -> k.toVariable}
              val freshToValue = vd.map{ v =>
                oldToFresh(v) -> defaultValue(v.getType)
              }.toMap
              val bodyWithFreshVariables = exprOps.replaceFromSymbols(oldToFresh.mapValues(_.toVariable), body)
              val oldToValue = oldToFresh.mapValues(freshToValue)

              val simplifiedExpectedBody = simplify(exprOps.replaceFromSymbols(oldToValue, expectedBody))
              for {pf <- repair(ProgramFormula(bodyWithFreshVariables,
                Formula(freshToValue ++ freeVars.map(fv => fv -> currentValues(fv)).toMap)),
                  newOutProgram.subExpr(simplifiedExpectedBody))
              } yield {
                  val ProgramFormula(newBody, f) = pf
                  Log(s"Going to test if lambda can be repaired using $newBody, $f, $freshToValue")
                  val newFreevarAssignments = freeVars.flatMap(fv => f.known.get(fv).map(res => fv -> res)).toMap
                  val newConstraint = f combineWith Formula(freshToValue)
                  Log(s"Returning lambda using $newBody, $f, $freshToValue, \n$newFreevarAssignments")
                  val fullNewBody = exprOps.replaceFromSymbols(freshToOld, newBody)

                  ProgramFormula(Lambda(vd, fullNewBody),
                    Formula(newFreevarAssignments) combineWith newConstraint) /: Log
                }
            case v: Variable =>
              Stream(ProgramFormula(v))
            case _ => ???
            }
          }

        // Variables are assigned the given value.
        case v@Variable(id, tpe, flags) =>
          newOutProgram match {
            case ProgramFormula.StringInsert(left, inserted, right) =>
              Stream(ProgramFormula(v, Formula(v === StringLiteral(left + inserted + right))))
            case ProgramFormula.StringDelete(left, right) =>
              Stream(ProgramFormula(v, Formula(v === StringLiteral(left + right))))
            case _ =>
              Stream(ProgramFormula(v, Formula(v === newOut) combineWith newOutFormula))
          }

        case Let(vd, expr, body) =>
          repair(ProgramFormula(Application(Lambda(Seq(vd), body), Seq(expr)), program.formula),
            newOutProgram).map {
            case ProgramFormula(Application(Lambda(Seq(vd), body), Seq(expr)), f) =>
              ProgramFormula(Let(vd, expr, body), f)
            case e  => throw new Exception(s"Don't know how to get a Let back from $e")
          }

        case StringConcat(expr1, expr2) =>
          ifEmpty(for(pf <- repair(program.subExpr(FunctionInvocation(StringConcatReverser.identifier, Nil,
            Seq(expr1, expr2))), newOutProgram)) yield {
            pf match {
              case ProgramFormula(FunctionInvocation(StringConcatReverser.identifier, Nil, Seq(x, y)), f) =>
                ProgramFormula(StringConcat(x, y), f)
            }
          }){
            val constraint = newOut === function
            Stream(ProgramFormula(function,
              Formula(unknownConstraints=constraint)))
          }

        case ADT(adtType@ADTType(tp, tpArgs), argsIn) =>
          newOut match {
            case Variable(ProgramFormula.subtree, tpe, s) =>
              val treeVar = Variable(ProgramFormula.tree, tpe, s)
              newOutFormula.findConstraintValue(treeVar) match {
                case Some(originalTree) =>
                  originalTree match {
                    case Variable(vid, _, _) if vid == ProgramFormula.subtree => // End of it, no change to make.
                      return Stream(program.withoutConstraints())
                    case ADT(adtType2@ADTType(tp2, tpArgs2), argsIn2) =>
                      if(adtType != adtType2) throw new Exception(s"Not the same type $adtType != $adtType2")
                      val i = argsIn2.indexWhere(argIn => exprOps.exists{
                        case k if k == Variable(ProgramFormula.subtree, tpe, s) => true
                        case _ => false
                      }(argIn))
                      if(i == -1) throw new Exception(s"Could not find subtree in: $originalTree")

                      repair(program.subExpr(argsIn(i)),
                        ProgramFormula(newOut, treeVar === argsIn2(i)))
                    case _ => throw new Exception(s"Not an ADT or the subtree: $originalTree")
                  }
                case None => throw new Exception(s"Could not find value of ${ValDef(ProgramFormula.tree, tpe, s)} in $newOutFormula")
              }
            case v: Variable =>
              Stream(ProgramFormula(v))
            case ADT(ADTType(tp2, tpArgs2), argsOut) if tp2 == tp && tpArgs2 == tpArgs && functionValue != newOut => // Same type ! Maybe the arguments will change or move.
              val seqOfStreamSolutions = argsIn.zip(argsOut).map { case (aFun, aVal) =>
                repair(ProgramFormula(aFun, program.formula), newOutProgram.subExpr(aVal))
              }
              val streamOfSeqSolutions = inox.utils.StreamUtils.cartesianProduct(seqOfStreamSolutions)
              for {seq <- streamOfSeqSolutions
                   _ = Log(s"combineResults($seq, $currentValues)")
                   (newArgs, assignments) = combineResults(seq, currentValues)
              } yield {
                ProgramFormula(ADT(ADTType(tp2, tpArgs2), newArgs), assignments)
              }
            case ADT(ADTType(tp2, tpArgs2), args2) => Stream.empty // Wrapping already handled.

            case a => // Another value in the type hierarchy. But Maybe sub-trees are shared !
              throw new Exception(s"Don't know how to handle this case : $a is supposed to be put in place of a ${tp}")
          }

        case as@ADTSelector(adt, selector) =>
          val originalAdtValue = evalWithCache(letm(currentValues) in adt).asInstanceOf[ADT]
          val constructor = as.constructor.get
          val fields = constructor.fields
          val index = as.selectorIndex
          val vds = fields.map{ fd => ValDef(FreshIdentifier("x", true), fd.getType, Set())}
          val constraints = vds.zipWithIndex map {
            case (vd, i) => if(i == index) {
              vd.toVariable === newOut
            } else {
              E(Utils.maybe)(vd.toVariable === originalAdtValue.args(i))
            }
          }
          val newConstraint = and(constraints : _*)
          val newVarsInConstraint = exprOps.variablesOf(newConstraint).map(_.toVal)

          for{ pf <- repair(program.subExpr(adt),
            newOutProgram.subExpr(ADT(ADTType(constructor.id, constructor.tps), vds.map(_.toVariable)))) } yield {
            pf.wrap(x => ADTSelector(x, selector)) combineWith Formula(
              unknownConstraints = newConstraint)
          }

        case MapApply(map, key) => // Variant of ADT selection.
          val map_v = evalWithCache(letm(currentValues) in map).asInstanceOf[FiniteMap] //originalAdtValue
          val key_v = evalWithCache(letm(currentValues) in key)

          val defaultValue = map_v.default

          val vds = map_v.pairs.map{ case (k, v) => (k, ValDef(FreshIdentifier("x", true), map_v.valueType, Set()))}
          var found = false
          val constraints = (vds map {
            case (k, vd) => if(k == key_v) {
              found = true
              vd.toVariable === newOut
            } else {
              E(Utils.maybe)(vd.toVariable === evalWithCache(MapApply(map_v, k)))
            }
          })
          val finiteMapRepair = if (!found) { // We should not change the default, rather add a new entry.
            FiniteMap(vds.map{x => (x._1, x._2.toVariable)} :+ (key_v -> newOut)
              , map_v.default, map_v.keyType, map_v.valueType)
          } else {
            FiniteMap(vds.map{x => (x._1, x._2.toVariable)}, map_v.default, map_v.keyType, map_v.valueType)
          }

          val newConstraint = and(constraints : _*)
          val newVariablesConstraints = exprOps.variablesOf(newConstraint).map(_.toVal)

          for{ pf <- repair(program.subExpr(map), newOutProgram.subExpr(finiteMapRepair)) } yield {
            pf.wrap(x => MapApply(x, key)) combineWith Formula(
              unknownConstraints = newConstraint)
          }

        case Application(lambdaExpr, arguments) =>
          val originalValue = (lambdaExpr match {
            case v: Variable => currentValues.getOrElse(v.toVal, evalWithCache(letm(currentValues) in v))
            case l: Lambda => l
            case l => evalWithCache(letm(currentValues) in l)
          }) /: Log.Original_Value
          originalValue match {
            case l@Lambda(argNames, body) =>
              val freshArgsNames = argNames.map(vd => ValDef(FreshIdentifier(vd.id.name, true), vd.tpe, vd.flags))
              val freshBody = exprOps.replaceFromSymbols(argNames.zip(freshArgsNames.map(_.toVariable)).toMap, body)
              val oldToFresh = argNames.zip(freshArgsNames).toMap
              val freshToOld = freshArgsNames.zip(argNames.map(_.toVariable)).toMap
              val argumentValues = argNames.zip(arguments.map(arg => evalWithCache(letm(currentValues) in arg))).toMap
              val freshArgumentValues = argumentValues.map{ case (k,v) => oldToFresh(k) -> v}
              val freshFormula = Formula(freshArgumentValues)
              val newpf = (program.subExpr(freshBody) combineWith freshFormula).wrappingEnabled
              for {pf <-
                     repair(newpf, newOutProgram)  /::
                       Log.prefix(s"For repair$stackLevel, recovered:\n")
                   ProgramFormula(newBodyFresh, newBodyFreshFormula) = pf
                   newBody = exprOps.replaceFromSymbols(freshToOld, newBodyFresh)
                   isSameBody = (newBody == body)              /: Log.isSameBody
                   args <-
                     combineArguments(program combineWith newBodyFreshFormula,
                       arguments.zip(freshArgsNames).map { case (arg, v) =>
                      val expected = newBodyFreshFormula.getOrElse(v, argumentValues(freshToOld(v).toVal))
                      (arg, newOutProgram.subExpr(expected))
                     })
                   (newArguments, newArgumentsFormula) = args
                   newLambda = if (isSameBody) l else Lambda(argNames, newBody)
                   pfLambda <- lambdaExpr match {
                     case v: Variable => Stream(ProgramFormula(v, (
                       if(isSameBody) Formula() else
                         Formula(Map(v.toVal -> newLambda)))))
                     case l => repair(ProgramFormula(l, program.formula), newOutProgram.subExpr(newLambda))
                   }
                   ProgramFormula(newAppliee, lambdaRepairFormula) = pfLambda
                   finalApplication = Application(newAppliee, newArguments)           /: Log.prefix("finalApplication")
              } yield {
                val combinedFormula = newBodyFreshFormula combineWith lambdaRepairFormula combineWith newArgumentsFormula
                Log.prefix("[return] ")  :=
                ProgramFormula(finalApplication: Expr, combinedFormula)
              }
            case _ => throw new Exception(s"Don't know how to handle this case : $function of type ${function.getClass.getName}")
          }

        case funInv@FunctionInvocation(f, tpes, args) =>
          // We need to reverse the invocation arguments.
          reversions.get(f) match {
            case None => Stream.empty  /: Log.prefix(s"No function $f reversible for : $funInv.\nIt evaluates to:\n$functionValue.")
            case Some(reverser) =>
              val argsValue = args.map(arg => evalWithCache(letm(currentValues) in arg))
              val lenseResult = reverser.put(tpes)(argsValue, newOutProgram)
              for{l <- lenseResult; (newArgsValues, newForm) = l
                  a <- combineArguments(program, args.zip(newArgsValues))
                  (newArguments, newArgumentsFormula) = a
              } yield {
                val formula = newForm combineWith newArgumentsFormula
                ProgramFormula(FunctionInvocation(f, tpes, newArguments), formula)
              }
          }
        case SetAdd(sExpr, elem) =>
          val sExpr_v = evalWithCache(letm(currentValues) in sExpr)
          val elem_v = evalWithCache(letm(currentValues) in elem)
          val FiniteSet(vs, tpe) = sExpr_v
          val FiniteSet(vsNew, _) = newOut
          val vsSet = vs.toSet
          val vsNewSet = vsNew.toSet
          val maybeAddedElements = vsNewSet -- vsSet
          val maybeRemovedElements = vsSet -- vsNewSet
          val (changedElements, added, removed) = if(maybeAddedElements.size == 1 && maybeRemovedElements.size == 1) {
            (maybeRemovedElements.headOption.zip(maybeAddedElements.headOption).headOption: Option[(Expr, Expr)], Set[Expr](), Set[Expr]())
          } else
            (None: Option[(Expr, Expr)], maybeAddedElements: Set[Expr], maybeRemovedElements: Set[Expr])
          Log(s"Added $added, Removed $removed, changed: $changedElements")
          changedElements match {
            case Some((old, fresh)) =>
              (if(vsSet contains old) {
                Log.prefix("#1") :=
                  (for(pf <- repair(program.subExpr(sExpr),
                  newOutProgram.subExpr(FiniteSet((vsSet - old + fresh).toSeq, tpe)))) yield {
                  pf.wrap(x => SetAdd(x, elem))
                })
              } else Stream.empty) #::: (
                Log.prefix("#2") :=
                  (if(elem_v == old) {
                  for(pf <- repair(program.subExpr(elem), newOutProgram.subExpr(fresh))) yield {
                    pf.wrap(x => SetAdd(sExpr, x))
                  }
                } else Stream.empty)
              )
            case None => // Just added and removed elements.
              if(removed.isEmpty) { // Just added elements.
                for(pf <- repair(program.subExpr(sExpr),
                  newOutProgram.subExpr(FiniteSet((vsSet ++ (added - elem_v)).toSeq, tpe)))) yield {
                  pf.wrap(x => SetAdd(x, elem))
                }
              } else {
                if(removed contains elem_v) { // We replace SetAdd(f, v) by f
                  for(pf <- repair(program.subExpr(sExpr),
                    newOutProgram.subExpr(FiniteSet(vsSet.toSeq, tpe))
                  )) yield pf
                } else { // All changes happened in the single set.
                  for(pf <- repair(program.subExpr(sExpr),
                    newOutProgram.subExpr(FiniteSet((vsSet ++ (added-elem_v) -- removed).toSeq, tpe))
                  )) yield pf.wrap(x => SetAdd(x, elem))
                }
              }
          }
        case IfExpr(cond, thenn, elze) =>
          val cond_v = evalWithCache(letm(currentValues) in cond)
          cond_v match {
            case BooleanLiteral(true) =>
              for(pf <- repair(program.subExpr(thenn), newOutProgram)) yield
                pf.wrap(x => IfExpr(cond, x, elze))
            case BooleanLiteral(false) =>
              for(pf <- repair(program.subExpr(elze), newOutProgram)) yield
                pf.wrap(x => IfExpr(cond, thenn, x))
            case _ => throw new Exception(s"Not a boolean: $cond_v")
          }
        case anyExpr =>
          Log(s"Don't know how to handle this case : $anyExpr of type ${anyExpr.getClass.getName},\nIt evaluates to:\n$functionValue.")
          Stream.empty
      }
    } #::: {Log(s"Finished repair$stackLevel"); Stream.empty[ProgramFormula]}  /:: Log.prefix(s"@return for repair$stackLevel(\n  $program\n, $newOut):\n~>")
  }

  /** Given a sequence of (arguments expression, expectedValue),
      returns the cartesian product of all argument programs and solutions. */
  private def combineArguments(pf: ProgramFormula,
      arguments: Seq[(Expr, ProgramFormula)])(implicit symbols: Symbols, cache: Cache): Stream[(Seq[Expr], Formula)] = {
    Log(s"combining arguments for $pf")
    val argumentsReversed = arguments.map { case (arg, expected) =>
      Log(s" repairing argument $arg should equal $expected")
      repair(ProgramFormula(arg, pf.formula), expected)
    }
    for ( r <- inox.utils.StreamUtils.cartesianProduct(argumentsReversed)) yield {
     (r.map(_.expr),
       (Formula() /: r) { case (f, pfr) => f combineWith pfr.formula })//r.map(_.formula))
    }
  }

  // Given a ProgramFormula for each of the fields, returns a list of expr and a single formulas
  private def combineResults(seq: List[ProgramFormula], currentValues: Map[ValDef,Expr])
            (implicit symbols: Symbols, cache: Cache): (List[Expr], Formula) = {
    val (lb, f) = ((ListBuffer[Expr](), Formula()) /: seq) {
      case total@((ls, f1), (ProgramFormula(l, f2))) =>
        (ls += l, f1 combineWith f2)
    }
    (lb.toList, f)
  }


  /** Simple function returning true if the given expression is a value. */
  @inline private def isValue(e: Expr): Boolean = e match {
    case l: Lambda => (exprOps.variablesOf(l.body).map(_.toVal) -- l.args).isEmpty
    case _: Literal[_] => true
    case ADT(_, a) => a.forall(isValue _)
    case FiniteMap(pairs, default, _, _) => pairs.forall(x => isValue(x._1) && isValue(x._2)) && isValue(default)
    case FiniteBag(elements, _) => elements.forall(x => isValue(x._1) && isValue(x._2))
    case FiniteSet(elements, _) => elements.forall(isValue _)
    case _ => false
  }

  /* Example:
    function = v
    functionValue = Element("b", List(), List(), List())
    newOut = Element("div", List(Element("b", List(), List(), List())), List(), List())
    result: Element("div", List(v), List(), List())
  * */
  private def maybeWrap(program: ProgramFormula, newOut: Expr, functionValue: Expr)(implicit symbols: Symbols): Stream[ProgramFormula] = {
    val function = program.expr
    if(functionValue == newOut) return Stream.empty[ProgramFormula] // Value returned in maybeUnwrap

    val containsFunctionValue = exprOps.exists {
      case t if t == functionValue => true
      case _ => false
    } _

    // Checks if the old value is inside the new value, in which case we add a wrapper.
    if (containsFunctionValue(newOut)) {
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
      if(canWrap) {
        // We wrap the computation of functionValue with ADT construction
        val newFunction = exprOps.postMap {
          case t if t == functionValue => Some(function)
          case _ => None
        }(newOut)
        val variables = program.formula.varsToAssign ++ program.freeVars
        val constraintExpression = program.formula.unknownConstraints
        val constraintFreeVariables = exprOps.variablesOf(constraintExpression).map(_.toVal)

        val (constraining, unconstrained) = variables.partition(constraintFreeVariables)

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
  private def maybeUnwrap(program: ProgramFormula, newOut: Expr, functionValue: Expr)(implicit symbols: Symbols): Stream[ProgramFormula] = {
    val function = program.expr
    if(functionValue == newOut) {
      Log("@return unwrapped")
      return Stream(program.withoutConstraints())
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
          maybeUnwrap(ProgramFormula(args(i), program.formula), newOut, arg)
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
      return Stream(program.withoutConstraints())
    }
    newOut match {
      case StringLiteral(s) =>
        function match {
          case StringLiteral(_) => Stream.empty // We can always replace the StringLiteral later
          //case StringConcat(_, _) => Stream.empty // We can always add the constant to a sub-expression, to avoid duplicate programs
          case _ =>
            functionValue match {
              case StringLiteral(t) =>((
                if(s.startsWith(t)) {
                  Stream(ProgramFormula(StringConcat(function, StringLiteral(s.substring(t.length)))))
                } else Stream.empty) #::: (
                if(s.endsWith(t)) {
                  Stream(ProgramFormula(StringConcat(StringLiteral(s.substring(0, s.length - t.length)), function)))
                } else Stream.empty
                )) /:: Log.prefix("@return wrapped: ")
              case _ => Stream.empty
            }
        }
      case _ => Stream.empty
    }
  }

  /* Example:
    function = "Therefore, " + f(a) + v + "boss"
    functionValue = "Therefore, I am the boss"
    newOut =  "I am the boss"
    result: f(a) + v + "boss" (we remove the empty string)
  * */
  /*private def maybeUnwrapString(program: ProgramFormula, newOut: Expr, functionValue: Expr)(implicit symbols: Symbols): Stream[ProgramFormula] = {
    val function = program.program
    if(functionValue == newOut) return Stream.empty

    def dropRightIfPossible(lReverse: List[Expr], toRemoveRight: String): Option[List[Expr]] =
      if(toRemoveRight == "") Some(lReverse.reverse) else lReverse match {
      case Nil => None
      case StringLiteral(last) :: lReverseTail =>
        if(toRemoveRight.endsWith(last))
          dropRightIfPossible(lReverseTail, toRemoveRight.substring(0, last.length))
        else if(last.endsWith(toRemoveRight))
          Some((StringLiteral(last.substring(0, last.length - toRemoveRight.length)) :: lReverseTail).reverse)
        else None
      case _ => None
    }

    def dropLeftIfPossible(l: List[Expr], toRemoveLeft: String): Option[List[Expr]] =
      if(toRemoveLeft == "") Some(l) else l match {
        case Nil => None
        case StringLiteral(first) :: lTail =>
          if(toRemoveLeft.startsWith(first))
            dropLeftIfPossible(lTail, toRemoveLeft.substring(0, first.length))
          else if(first.startsWith(toRemoveLeft))
            Some(StringLiteral(first.substring(toRemoveLeft.length)) :: lTail)
          else None
        case _ => None
      }

    newOut match {
      case StringLiteral(s) =>
        functionValue match {
        case StringLiteral(t) =>(
          if(t.startsWith(s)) {
            val StringConcats(seq) = function
            dropRightIfPossible(seq.reverse, t.substring(s.length)).toStream.map(x => ProgramFormula(StringConcats(x), Formula(known = Map(), varsToAssign = Set(), program.freeVars)))
          } else Stream.empty) #::: (
          if(t.endsWith(s)) {
            val StringConcats(seq) = function
            dropLeftIfPossible(seq, t.substring(0, t.length - s.length)).toStream.map(x => ProgramFormula(StringConcats(x), Formula(known = Map(), varsToAssign = Set(), program.freeVars)))
          } else Stream.empty
          )
          case _ => Stream.empty
        }
      case _ => Stream.empty
    }
  }*/
}
