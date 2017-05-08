package perfect

import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.ReverseProgram.{Cache, maybeEvalWithCache, repair}
import perfect.StringConcatExtended._
import perfect.Utils.optVar
import semanticlenses._

import scala.collection.mutable.ListBuffer

/**
  * Created by Mikael on 06/04/2017.
  */
object ProgramFormula {
  import Utils._
  import InoxConvertible._
  // For semantic insert for string
  // ProgramFormula(leftTreeStr +& "The Insertion" +& rightTreeStr,
  //   tree == leftTreeStr +& rightTreeStr && leftTreeStr == "String to the left && rightTreeStr = "String to the right"

  def apply(e: Expr, f: (Variable, KnownValue)): ProgramFormula = ProgramFormula(e, Formula(Map(f)))



  trait CustomProgramFormula {
    def funDef: FunDef

    def Eval: {
      def unapply(e: Expr)(implicit symbols: Symbols): Option[Expr]
    }
  }

  trait MergeProgramFormula {
    def merge(e1: Expr, e2: Expr)(implicit symbols: Symbols): Option[(Expr, Seq[(Variable, KnownValue)])]
  }

  /** Inserts a variable for a given selected text. Simpler than CloneTextMultiple. */
  object CloneText  { ct =>
    private val Cloned = FreshIdentifier("cloned")

    def apply(left: String, text: String, right: String, insertedVar: Variable = Variable(FreshIdentifier(""), StringType, Set()))(implicit symbols: Symbols): ProgramFormula = {
      val variable = if(insertedVar.id.name == "") Var(text) else insertedVar
      CloneTextMultiple(left, List((text, variable, right)))
    }
    object Var {
      /** Creates a variable from the text. If nothing found, uses i. */
      def apply(text: String, conflicts: Seq[String] = Nil): Variable = {
        val word = text.split("\\W+")
          .filter(x => x.nonEmpty && x.charAt(0).isLetter).mkString("_").take(15).toLowerCase()
        val default = if(word.isEmpty) "x" else word
        val finalName = Utils.uniqueName(default, conflicts.toSet)
        Variable(FreshIdentifier(finalName), StringType, Set())
      }
    }
  }

  object CloneTextMultiple {
    def apply(left: String, textVarRights: List[(String, Variable, String)])(implicit symbols: Symbols): ProgramFormula =
      ProgramFormula(Expr(left, textVarRights))

    object Expr {
      def apply(left: String, textVarRights: List[(String, Variable, String)])(implicit symbols: Symbols) = {
        val before = ((StringLiteral(left): Expr) /: textVarRights) {
          case (e: Expr, (middle, v, right)) => e +<>& v +<>& StringLiteral(right)
        }
        PatternMatch.Expr(before, textVarRights.map(x => x._2 -> StringLiteral(x._1)), true)
      }
      def unapply(e: Expr)(implicit symbols: Symbols): Option[(String, List[(String, Variable, String)])] = e match {
        case PatternMatch.Expr(StringConcats.Exhaustive(strs), variables, true) =>
          def getVarValue(v: Variable): String = variables.collectFirst {
            case (v2, StringLiteral(s)) if v2 == v => s
          }.get

          def unbuild(e: List[Expr]): Option[(String, List[(String, Variable, String)])] = e match {
            case Nil => Some(("", Nil))
            case StringLiteral(text) :: tail => unbuild(tail).map{ case (left, l) =>
             ((text+left), l)
            }
            case (v: Variable)::tail => unbuild(tail).map{ case (left, l) =>
              ("", (getVarValue(v), v, left)::l)
            }
            case _ => None
          }
          unbuild(strs)
        case _ => None
      }

      private def SplitVar(v1: Variable, inserted: Set[Variable]): (Variable, Variable) = {
        val v1p1 = CloneText.Var(v1.id.name, inserted.toSeq.map(_.id.name) ++ Seq(v1.id.name))
        val v1p2 = CloneText.Var(v1.id.name, inserted.toSeq.map(_.id.name) ++ Seq(v1.id.name, v1p1.id.name))
        (v1p1, v1p2)
      }
      def merge(left1: String, textVarRight1: List[(String, Variable, String)],
                left2: String, textVarRight2: List[(String, Variable, String)], inserted: Set[Variable] = Set())(implicit symbols: Symbols): Option[(Expr, Seq[(Variable, KnownValue)])] = {
        Log(s"merge with inserted ${inserted}\n1. ($left1, $textVarRight1)\n2. ($left2, $textVarRight2)")
        if(left1.length > 0 && left2.length > 0) {
          if(left1.length <= left2.length) {
            assert(left2.startsWith(left1))
            merge("", textVarRight1,
              left2.substring(0, left1.length), textVarRight2, inserted).map{
              case (Expr(newLeft1, newTextVarRight1), vk) =>
                (Expr(left1 + newLeft1, newTextVarRight1), vk)
            }
          } else { // if(left1.length > left2.length)
            merge(left2, textVarRight2, left1, textVarRight1, inserted)
          }
        } else {
          // At least one of left1 and left2 is empty.
          (textVarRight1, textVarRight2) match {
            case (Nil, Nil) if left1 == left2 =>
              Some((apply(left1, Nil), Nil))
            case (Nil, textVarRight2) if left1.startsWith(left2) =>
              Some((apply(left2, textVarRight2), Nil))
            case (textVarRight1, Nil) if left2.startsWith(left1) =>
              Some((apply(left1, textVarRight1), Nil))
            case ((middle1, v1, right1) :: tail1, (middle2, v2, right2) :: tail2) =>
              if (left1.length == 0) {
                if (left2.startsWith(middle1)) {
                  // We can insert the first variable in place of left2.
                  val updatedLeft2 = left2.substring(middle1.length)
                  val updatedRight1 = right1
                  merge(updatedRight1, tail1, updatedLeft2, textVarRight2, inserted).map {
                    case (Expr(leftNew, textVarRightNew), mp) =>
                      (Expr(left1, (middle1, v1, leftNew) :: textVarRightNew), mp)
                  }
                } else if(left2.length == 0) { // Overlapping between variables
                  if(middle1.length == middle2.length) {
                    if(inserted(v1)) {
                      if(inserted(v2)) {
                        Log("[internal warning] tried to merge two inserted variables, makes no sense.")
                        None
                      } else {
                        merge(right1, tail1, right2, tail2, inserted) map {
                          case (Expr(leftNew, textVarRightNew), mp) =>
                            (Expr("", (middle1, v1, leftNew)::textVarRightNew),
                              (v2 -> InsertVariable(v1)) +: mp)
                        }
                      }
                    } else {
                      if(inserted(v2)) {
                        merge(left2, textVarRight2, left1, textVarRight1, inserted)
                      } else { // We insert a new variable and link the two other variables.
                        val v = CloneText.Var(v1.id.name, Seq(v2.id.name))
                        merge(right1, tail1, right2, tail2, inserted) map {
                          case (Expr(leftNew, textVarRightNew), mp) =>
                            (Expr("", (middle1, v, leftNew)::textVarRightNew),
                              (v1 -> InsertVariable(v)) +: (v2 -> InsertVariable(v)) +: mp)
                        }
                      }
                    }
                  } else if(middle1.length < middle2.length) {
                    if(inserted(v1)) {
                      if(inserted(v2)) {
                        Log("[internal warning] tried to merge two inserted variables, makes no sense.")
                        None
                      } else {
                        // We split v2 into a second variable.
                        val (_, v2p2) = SplitVar(v2, inserted)
                        val news = v2 -> InsertVariable(v1 +& v2p2)
                        val positionSplit = middle1.length
                        val newMiddle2 = middle2.substring(positionSplit)
                        merge(right1, tail1, "", (newMiddle2, v2p2, right2)::tail2, inserted) map {
                          case (Expr(leftNew, textVarRightNew), mp) =>
                            (Expr("", (middle1, v1, leftNew)::textVarRightNew), news +: mp)
                        }
                      }
                    } else {
                      val (v2p1, v2p2) = SplitVar(v2, inserted)
                      val news = v2 -> InsertVariable(v2p1 +& v2p2)
                      val position = middle1.length
                      val middle21 = middle2.substring(0, position)
                      val middle22 = middle2.substring(position)
                      merge(left1, textVarRight1,
                        left2, (middle21, v2p1, "") :: (middle22, v2p2, right2) :: tail2, inserted ++ Seq(v2p1, v2p2)
                      ) map {
                        case (ctm, mp) => (ctm, news +: mp)
                      }
                    }
                  } else {
                    merge(left2, textVarRight2, left1, textVarRight1, inserted)
                  }
                } else { // Partial overlapping of a variable on the left string of the next.
                  assert(middle1.startsWith(left2)) // We need to introduce one variable for the overlap.
                  val (v1p1, v1p2) = SplitVar(v1, inserted)
                  val news = v1 -> InsertVariable(v1p1 +& v1p2)
                  val positionSplit = left2.length
                  val newMiddle1 = middle1.substring(0, positionSplit) // should equal left2.
                  val newLeft1 = middle1.substring(positionSplit)

                  merge(left1, (newMiddle1, v1p1, "") :: (newLeft1, v1p2, right1) :: tail1,
                    left2, textVarRight2, inserted ++ Seq(v1p1, v1p2)
                  ).map {
                    case (ctm, mp) =>
                      (ctm, news +: mp)
                  }
                }
              } else { //if (left2.length == 0)
                merge(left2, textVarRight2, left1, textVarRight1, inserted)
              }
          }
        }
      } /: Log.prefix(s"merge with inserted ${inserted}\n1. ($left1, $textVarRight1)\n2. ($left2, $textVarRight2) =\n")
    }
  }

  val customProgramFormulas = List[CustomProgramFormula](
    TreeWrap,
    TreeUnwrap,
    StringInsert,
    ListInsert,
    PatternMatch,
    PasteVariable,
    TreeModification
  )

  val mergeProgramFormula = List[MergeProgramFormula](
    ADTExpr,
    PatternMatch
  )

  val customFunDefs = customProgramFormulas.map(_.funDef)

  /** Given a sequence of (arguments expression, expectedValue),
      returns the cartesian product of all argument programs and solutions. */
  def repairArguments(pf: ProgramFormula,
       arguments: Seq[(Expr, ProgramFormula)])(implicit symbols: Symbols, cache: Cache): Stream[(Seq[Expr], Formula)] = {
    Log(s"combining arguments for $pf")
    val argumentsReversed = arguments.map { case (arg, expected) =>
      Log(s"repairing argument $arg should equal $expected")
      repair(ProgramFormula(arg, pf.formula), expected)
    }
    regroupArguments(argumentsReversed)
  }

  // Given a ProgramFormula for each of the fields, returns a list of expr and a single formulas
  def regroupArguments(arguments: Seq[Stream[ProgramFormula]])
  (implicit symbols: Symbols, cache: Cache): Stream[(List[Expr], Formula)] = {
    inox.utils.StreamUtils.cartesianProduct(arguments).map(combineResults)
  }

  // Given a ProgramFormula for each of the fields, returns a list of expr and a single formulas
  def combineResults(seq: List[ProgramFormula])
                    (implicit symbols: Symbols, cache: Cache): (List[Expr], Formula) = {
    val (lb, f) = ((ListBuffer[Expr](), Formula()) /: seq) {
      case total@((ls, f1), (ProgramFormula(l, f2))) =>
        (ls += l, f1 combineWith f2)
    }
    (lb.toList, f)
  }
}

case class ProgramFormula(expr: Expr, formula: Formula = Formula()) {
  lazy val freeVars: Set[Variable] = exprOps.variablesOf(expr)
  lazy val unchanged: Set[Variable] = freeVars -- formula.varsToAssign

  override def toString = expr.toString + s" [$formula]" + (if(canDoWrapping) " (wrapping enabled)" else "") + (if(isWrappingLowPriority) " (avoid wrap)" else "")
  var canDoWrapping = false

  def wrappingEnabled: this.type = {
    this.canDoWrapping = true
    this
  }

  def withComputedValue(e: Expr): this.type = {
    givenValue = Some(e)
    this
  }
  def withComputedValue(e: Option[Expr]): this.type = {
    givenValue = givenValue.orElse(e)
    this
  }

  lazy val simplifiedExpr: Expr = optVar(expr).flatMap(formula.findConstraintValue).getOrElse(expr)

  // Can be set-up externally to bypass the computation of the function value.
  // Must be set before a call to functionValue using .withComputedValue
  private var givenValue: Option[Expr] = None

  lazy val bodyDefinition: Option[Expr] = formula.assignments.map(f => f(expr))

  def getFunctionValue(implicit cache: Cache, symbols: Symbols): Option[Expr] = {
    givenValue match {
      case Some(e) => givenValue
      case None =>
        if(Utils.isValue(expr)) {
          givenValue = Some(expr)
          givenValue
        } else {
          formula.assignments match {
            case Some(f) =>
              val res = maybeEvalWithCache(f(expr))
              givenValue = res
              res
            case None =>
              expr match {
                case FunctionInvocation(_, _, _) => None
                case _ =>
                  // Maybe we can generate the value out of the constraints still.
                  var tmp = expr
                  var prev = Set[Expr]()
                  while(exprOps.variablesOf(tmp).nonEmpty && !(prev contains tmp)) {
                    prev = prev + tmp
                    val mapping = exprOps.variablesOf(tmp).map { v =>
                      v.toVal -> formula.findConstraintValue(v).getOrElse(v)
                    }.toMap
                    tmp = exprOps.replaceFromSymbols(mapping, tmp)
                  }
                  if(exprOps.variablesOf(tmp).isEmpty) {
                    Some(tmp)
                  } else None
              }
          }
        }
    }
  }

  def functionValue(implicit cache: Cache, symbols: Symbols): Expr = {
    givenValue match {
      case Some(e) => e
      case None =>
        val res = {
          if((freeVars -- formula.known.keySet).nonEmpty) {
            throw new Exception(s"[Internal error] Tried to compute a function value but not all variables were known (only ${formula.known.keySet} are).\n$this")
          }
          formula.assignments.flatMap(wrapper => maybeEvalWithCache(wrapper(expr))).get
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

  var isWrappingLowPriority: Boolean = false

  def wrappingLowPriority(b: Boolean = true): this.type = {
    isWrappingLowPriority = true
    this
  }

  /** Replaces the expression with another, for defining sub-problems mostly. */
  def subExpr(f: Expr): ProgramFormula = {
    ProgramFormula(f, formula).wrappingLowPriority(isWrappingLowPriority)
  }

  /*def withoutConstraints(): ProgramFormula = {
    ProgramFormula(expr)
  }*/

  /** Returns the original assignments marked as original
    * Require known to be set. */
  def assignmentsAsOriginals(): ProgramFormula = {
    this.copy(formula = this.formula.assignmentsAsOriginals)
  }

  /** Augment this expr with the given formula */
  def combineWith(f: Formula)(implicit symbols: Symbols): ProgramFormula = {
    ProgramFormula(expr, formula combineWith f).wrappingLowPriority(isWrappingLowPriority)
  }

  /** Removes all insertVar from the formula and inserts them into the program.*/
  def insertVariables(): ProgramFormula = {
    val inserted: Map[Variable, KnownValue] = formula.known.collect[(Variable, KnownValue), Map[Variable, KnownValue]]{
      case (v, InsertVariable(e)) => (v, StrongValue(e))
    }
    val remaining = formula.known.filter{
      case (v, InsertVariable(e)) => false
      case _ => true
    }
    val newFormula = if(inserted.isEmpty) formula else formula.copy(known = remaining)
    val assignment = Formula(inserted).assignments

    if(inserted.nonEmpty && assignment.nonEmpty) {
      ProgramFormula(assignment.get(expr), newFormula)
    } else this
  }
}
