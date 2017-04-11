package perfect

import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.ReverseProgram.{Cache, evalWithCache, letm}
import perfect.StringConcatExtended._

/**
  * Created by Mikael on 06/04/2017.
  */
object ProgramFormula {
  import Utils._
  import InoxConvertible._
  // For semantic insert for string
  // ProgramFormula(leftTreeStr +& "The Insertion" +& rightTreeStr,
  //   tree == leftTreeStr +& rightTreeStr && leftTreeStr == "String to the left && rightTreeStr = "String to the right"

  def apply(e: Expr, f: Expr): ProgramFormula = ProgramFormula(e, Formula(f))

  trait CustomProgramFormula {
    def funDef: FunDef
  }

  object TreeWrap extends CustomProgramFormula {
    private val Wrap = FreshIdentifier("wrap")
    def apply(tree: Expr, wrapper: Expr => Expr)(implicit symbols: Symbols): ProgramFormula = {
      val tpe = tree.getType
      ProgramFormula(E(Wrap)(tpe)(\("tree"::tpe)(treeVar => wrapper(treeVar)), tree))
    }
    def unapply(pf: ProgramFormula)(implicit symbols: Symbols): Option[(Expr, Expr => Expr)] = {
      pf.expr match {
        case FunctionInvocation(Wrap, tpe, Seq(Lambda(Seq(treeVal), wtree), original)) =>
          Some((original, (vr: Expr) => exprOps.replaceFromSymbols(Map(treeVal -> vr),wtree)))
        case _ => None
      }
    }
    def funDef = mkFunDef(Wrap)("A"){ case Seq(tA) =>
      (Seq("wrapper"::FunctionType(Seq(tA), tA), "tree"::tA),
        tA, {
        case Seq(wrapper, tree) =>
          Application(wrapper, Seq(tree))
      })
    }
  }

  object TreeUnwrap extends CustomProgramFormula  {
    private val Unwrap = FreshIdentifier("unwrap")

    def apply(tpe: Type, original: Expr, argsInSequence: List[Identifier]): ProgramFormula = {
      ProgramFormula(E(Unwrap)(tpe)(
        original,
        \("unwrap"::tpe)(unwrap =>
          ((unwrap: Expr) /: argsInSequence){ case (e, i) => ADTSelector(e, i)}
        )
      ))
    }
    def unapply(pf: ProgramFormula)(implicit symbols: Symbols): Option[(Type, Expr, List[Identifier])] = {
      pf.expr match {
        case FunctionInvocation(Unwrap, Seq(tpe), Seq(original, Lambda(Seq(unwrapvd), adtselectors))) =>
          def unbuild(e: Expr): (Type, Expr, List[Identifier]) = e match {
            case ADTSelector(e, i) =>
              val (t, res, l) = unbuild(e)
              (t, res, l :+ i)
            case res => (tpe, original, Nil)
          }
          Some(unbuild(adtselectors))
        case _ => None
      }
    }

    def funDef = mkFunDef(Unwrap)("A"){ case Seq(tA) =>
      (Seq("original"::tA, "unwrapper"::FunctionType(Seq(tA), tA)),
        tA, {
        case Seq(original, unwrapper) =>
          Application(unwrapper, Seq(original))
      })
    }
  }

  /** To build and extract a StringInsert specification. Works for modifications as well */
  object StringInsert extends Enumeration with CustomProgramFormula  {
    private val InsertString = FreshIdentifier("insertString")

    type InsertDirection = Value
    val InsertToLeft, InsertToRight, InsertAutomatic = Value
    private object Direction {
      def unapply(s: String): Option[InsertDirection] =
        values.find(_.toString == s)
    }

    def computeDirection(left: String, s: String, right: String): InsertDirection = {
      val leftJump = ReverseProgram.StringConcatReverser.typeJump(left, s)
      val rightJump = ReverseProgram.StringConcatReverser.typeJump(s, right)
      if(leftJump < rightJump) {
        InsertToLeft
      } else if(leftJump > rightJump) {
        InsertToRight
      } else {
        InsertAutomatic
      }
    }

    /** Need a preference to attach to left or right. If not specified, will try to infer it from the expressions
      * @param left The untouched string to the left of the insertion (may have removals)
      * @param s The newly inserted string
      * @param right The untouched string to the right of the insertion (may have removals)
      * @param direction -1 if the insertion should be inserted to left, 1 to right, 0 if automatically guessed.
      **/
    def apply(left: String, s: String, right: String, direction: InsertDirection): ProgramFormula = {
      ProgramFormula(E(InsertString)(StringLiteral(left), StringLiteral(s), StringLiteral(right), StringLiteral(direction.toString)))
    }

    def unapply(f: ProgramFormula): Option[(String, String, String, InsertDirection)] = {
      f.expr match {
        case FunctionInvocation(InsertString, Seq(), Seq(
          StringLiteral(leftBefore), StringLiteral(inserted), StringLiteral(rightBefore), StringLiteral(Direction(direction))
        )) =>
          Some((leftBefore, inserted, rightBefore, direction))
        case _ =>
          None
      }
    }

    def funDef = mkFunDef(InsertString)(){ case _ =>
      (Seq("left"::StringType, "inserted"::StringType, "right"::StringType, "direction"::StringType),
        StringType,
        {
          case Seq(left, inserted, right, direction) =>
            left +& inserted +& right // Dummy
        })
    }
  }

  object ListInsert extends CustomProgramFormula  {
    private val InsertList = FreshIdentifier("insertList")
    def apply(tpe: Type, leftUnmodified: List[Expr], inserted: List[Expr], rightUnmodified: List[Expr], remaining: Expr/* = BooleanLiteral(true)*/): ProgramFormula = {
      ProgramFormula(
        E(InsertList)(tpe)(
          ListLiteral(leftUnmodified, tpe),
          ListLiteral(inserted, tpe),
          ListLiteral(rightUnmodified, tpe),
          StringLiteral(".") // Not used direction
        ), Formula(remaining))
    }

    def unapply(f: ProgramFormula): Option[(Type, List[Expr], List[Expr], List[Expr], Expr)] = {
      f.expr match {
        case FunctionInvocation(InsertList, Seq(tpe0), Seq(
          ListLiteral(leftBefore, _),
        ListLiteral(inserted, tpe3),
        ListLiteral(rightBefore, _),
        _)) =>
          Some((tpe0, leftBefore, inserted, rightBefore, f.formula.unknownConstraints))
        case _ => None
      }
    }

    def funDef = mkFunDef(InsertList)("A"){ case Seq(tA) =>
      (Seq("left"::T(Utils.list)(tA), "inserted"::T(Utils.list)(tA), "right"::T(Utils.list)(tA), "direction"::StringType),
        T(Utils.list)(tA), {
        case Seq(left, inserted, right, direction) =>
          E(Utils.listconcat)(tA)(E(Utils.listconcat)(tA)(
            left,
            inserted),
            right)
      })
    }
  }

  /** Inserts a variable for a given selected text.*/
  object CloneText extends CustomProgramFormula  { ct =>
    private val Cloned = FreshIdentifier("cloned")

    def apply(left: String, text: String, right: String, insertedVar: Variable = Variable(FreshIdentifier(""), StringType, Set())): ProgramFormula = {
      val variable = if(insertedVar.id.name == "") Var(text) else insertedVar
      //ProgramFormula(E(Cloned)(StringLiteral(left), StringLiteral(text), StringLiteral(right), variable))
      CloneTextMultiple(left, List((text, insertedVar, right)))
    }
    object Var {
      /** Creates a variable from the text. If nothing found, uses i. */
      def apply(text: String, conflicts: Seq[String] = Nil): Variable = {
        val word = text.split("\\W+")
          .filter(x => x.nonEmpty && x.charAt(0).isLetter).mkString("_").take(15).toLowerCase()
        val default = if(word.isEmpty) "x" else word
        var finalName = default
        var suffix = ""
        while(conflicts.exists(_ == finalName + suffix.reverse)) {
          val zs = suffix.takeWhile(c => c == 'z')
          val not_zs = suffix.drop(zs.length)
          val after_zs = if(not_zs.isEmpty) "a" else {
            (not_zs(0) + 1).toChar + not_zs.substring(1)
          }
          suffix = "a"*zs.length + after_zs
        }
        Variable(FreshIdentifier(finalName + suffix.reverse), StringType, Set())
      }
    }

    /*def unapply(f: ProgramFormula): Option[(String, String, String, Variable)] = {
      f.expr match {
        case FunctionInvocation(Cloned, Seq(), Seq(StringLiteral(left), StringLiteral(cloned), StringLiteral(right), v: Variable)) =>
          Some((left, cloned, right, v))
        case _ => None
      }
    }*/

    def funDef = mkFunDef(Cloned)(){ case _ =>
      (Seq("left"::StringType, "cloned"::StringType, "right"::StringType, "varname"::StringType),
        StringType,
        { case Seq(left, cloned, right, varname) =>
            left +& cloned +& right // Dummy
        })
    }
  }

  /** Inserts a variable for a given selected text.*/
  object CloneTextMultiple extends CustomProgramFormula  { ct =>
    private val ClonedMultiple = FreshIdentifier("clones")
    import ImplicitTuples._

    def createExpr(left: String, textVarRights: List[(String, Variable, String)]): Expr = {
      ((StringLiteral(left): Expr) /: textVarRights) {
        case (e: Expr, (middle, v, right)) => e +<>& v +<>& StringLiteral(right)
      }
    }

    def assignmentDirect(textVarRights: List[(String, Variable, String)]): (Expr => Expr) = { (e: Expr) =>
      (e /: textVarRights) {
        case (e: Expr, (middle, v, right)) => Let(v.toVal, StringLiteral(middle), e)
      }
    }

    def assignmentFormula(textVarRights: List[(String, Variable, String)]): Formula = {
      (Formula() /: textVarRights) {
        case (f, (middle, v, right)) => f combineWith Formula(E(insertvar)(v === StringLiteral(middle)))
      }
    }

    def merge(left1: String, textVarRight1: List[(String, Variable, String)],
              left2: String, textVarRight2: List[(String, Variable, String)]): Option[ProgramFormula] = {
      (textVarRight1, textVarRight2) match {
        case (Nil, Nil) if left1 == left2 =>
          Some(apply(left1, Nil))
        case (Nil, textVarRight2) if left1.startsWith(left2) =>
          Some(apply(left2, textVarRight2))
        case (textVarRight1, Nil) if left2.startsWith(left1) =>
          Some(apply(left1, textVarRight1))
        case ((middle1, v1, right1)::tail1, (middle2, v2, right2)::tail2) =>
          if(left1.length < left2.length) {
            if(left2.startsWith(left1+middle1)) {
              // We can insert the first variable in place of left2.
              val updatedLeft2 = left2.substring(left1.length+middle1.length)
              val updatedRight1 = if(updatedLeft2.length < right1.length) updatedLeft2 else right1
              merge(updatedRight1, tail1, updatedLeft2, textVarRight2).map{
                case CloneTextMultiple(leftNew, textVarRightNew) =>
                  CloneTextMultiple(left1, (middle1, v1, leftNew)::textVarRightNew)
              }
            } else None
          } else if(left1.length > left2.length) {
            merge(left2, textVarRight2, left1, textVarRight1)
          } else { // We don't know how to merge these two.
            None
          }

      }


    }


    def apply(left: String, textVarRight: List[(String, Variable, String)]): ProgramFormula = {
      ProgramFormula(E(ClonedMultiple)(
        StringLiteral(left),
        ListLiteral(textVarRight.map{ case (middle, v, right) =>
          _Tuple3(StringType, StringType, StringType)(StringLiteral(middle), v, StringLiteral(right))
        }, inoxTypeOf[(String, String, String)])))
    }

    def unapply(f: ProgramFormula): Option[(String, List[(String, Variable, String)])] = {
      f.expr match {
        case FunctionInvocation(ClonedMultiple, Seq(), Seq(StringLiteral(left), ListLiteral(textVarRightList, tpe))) =>
          def unbuild(e: List[Expr]): Option[List[(String, Variable, String)]] = e match {
            case Nil => Some(Nil)
            case ADT(_, Seq(StringLiteral(text), v: Variable, StringLiteral(right))) :: tail => unbuild(tail).map{ l =>
              (text, v, right)::l
            }
            case _ => None
          }
          unbuild(textVarRightList).map(x => (left, x))
        case _ => None
      }
    }

    private val string3 = T(tuple3)(StringType, StringType, StringType)

    def funDef = mkFunDef(ClonedMultiple)(){ case _ =>
      (Seq("left"::StringType, "textVarRight"::conversions.TList[(String, String, String)]),
        StringType,
        { case Seq(left, textVarRight) =>
          if_(textVarRight.isInstOf(T(cons)(string3))) {
            let("c"::T(cons)(string3), textVarRight.asInstOf(T(cons)(string3)))(c =>
              let("head"::string3, c.getField(head))( head =>
                FunctionInvocation(ClonedMultiple, Seq(),
                  Seq(left +& head.getField(_1) +& head.getField(_2),
                    c.getField(tail)
                  )
                )
              )
            )
          } else_ {
            left
          } // Dummy
        })
    }
  }

  /** Paste a previously cloned variable. Like  StringInsert but with a variable inside it. */
  object PasteVariable extends Enumeration with CustomProgramFormula  {
    private val Paste = FreshIdentifier("pastevariable")

    type PasteDirection = Value
    val PasteToLeft, PasteToRight, PasteAutomatic = Value
    private object Direction {
      def unapply(s: String): Option[PasteDirection] =
        values.find(_.toString == s)
    }
    def apply(left: String, insertedVar: Variable, originalVarValue: String, right: String, direction: PasteDirection): ProgramFormula = {
      ProgramFormula(E(Paste)(
        StringLiteral(left),
        insertedVar,
        StringLiteral(originalVarValue),
        StringLiteral(right),
        StringLiteral(direction.toString)
      ))
    }

    def unapply(f: ProgramFormula): Option[(String, Variable, String, String, PasteDirection)] = {
      f.expr match {
        case FunctionInvocation(Paste, Seq(), Seq(
        StringLiteral(leftBefore),
        inserted: Variable,
        StringLiteral(insertedValue),
        StringLiteral(rightBefore),
        StringLiteral(Direction(direction))
        )) =>
          Some((leftBefore, inserted, insertedValue, rightBefore, direction))
        case _ =>
          None
      }
    }

    def funDef = mkFunDef(Paste)(){ case _ =>
      (Seq("left"::StringType, "pasted"::StringType,  "originalvalue"::StringType, "right"::StringType, "direction"::StringType),
        StringType,
        {
          case Seq(left, pasted, originalvalue, right, direction) =>
            left +& originalvalue +& right // Dummy
        })
    }
  }

  val customProgramFormulas = List[CustomProgramFormula](
    TreeWrap,
    TreeUnwrap,
    StringInsert,
    ListInsert,
    CloneText,
    CloneTextMultiple,
    PasteVariable
  )

  val customFunDefs = customProgramFormulas.map(_.funDef)
}

case class ProgramFormula(expr: Expr, formula: Formula = Formula()) {
  lazy val freeVars: Set[ValDef] = exprOps.variablesOf(expr).map(_.toVal)
  lazy val unchanged: Set[ValDef] = freeVars -- formula.varsToAssign

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
              val res = try evalWithCache(f(expr)) catch {
                case e: Exception => return None
              }
              givenValue = Some(res)
              givenValue
            case _ => None
          }
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
    this.copy(formula = Formula(and(formula.known.toSeq.map{ case (k, v) => E(Utils.original)(k.toVariable === v) } :_*)))
  }

  /** Augment this expr with the given formula */
  def combineWith(f: Formula): ProgramFormula = {
    ProgramFormula(expr, formula combineWith f).wrappingLowPriority(isWrappingLowPriority)
  }

  /** Removes all insertVar from the formula and inserts them into the program.*/
  def insertVariables(): ProgramFormula = {
    val TopLevelAnds(ands) = formula.unknownConstraints
    val (insertedV, remaining) = ands.partition{
      case FunctionInvocation(Utils.insertvar, Seq(), Seq(Equals(v: Variable, e: Expr))) =>
        true
      case _ => false
    }
    val inserted = insertedV collect {
      case FunctionInvocation(Utils.insertvar, Seq(), Seq(m@Equals(v: Variable, e: Expr))) => m
    }
    val newFormula = if(insertedV.isEmpty) formula else Formula(and(remaining: _*))
    val newInserted = Formula(and(inserted :_*))
    val assignment = newInserted.assignments

    if(inserted.nonEmpty && assignment.nonEmpty) {
      ProgramFormula(assignment.get(expr), newFormula)
    } else this
  }
}
