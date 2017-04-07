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

  object TreeWrap {
    private val treeName = "treeWrap"
    def apply(tree: Expr, wrapper: Expr => Expr)(implicit symbols: Symbols): ProgramFormula = {
      val tpe = tree.getType
      val treeVar = Variable(FreshIdentifier(treeName, true), tpe, Set())
      ProgramFormula(Application(Lambda(Seq(treeVar.toVal), wrapper(treeVar)), Seq(tree)))
    }
    def unapply(pf: ProgramFormula)(implicit symbols: Symbols): Option[(Expr, Expr => Expr)] = {
      pf.expr match {
        case Application(Lambda(Seq(treeVal), wtree), Seq(original)) if treeVal.id.name == treeName =>
          Some((original, (vr: Expr) => exprOps.replaceFromSymbols(Map(treeVal -> vr),wtree)))
        case _ => None
      }
    }
  }

  object TreeUnwrap {
    private val unwrappedName = "unwrap"
    def apply(tpe: Type, original: Expr, argsInSequence: List[Identifier]): ProgramFormula = {
      val unwrappedVar = Variable(FreshIdentifier(unwrappedName, true), tpe, Set())
      ProgramFormula(unwrappedVar, unwrappedVar === (original /: argsInSequence){ case (e, i) => ADTSelector(e, i)}  )
    }
    def unapply(pf: ProgramFormula)(implicit symbols: Symbols): Option[(Type, Expr, List[Identifier])] = {
      pf.expr match {
        case v@Variable(id, tpe, _) if id.name == unwrappedName =>
          val adtselectors = pf.formula.findConstraintValue(v).getOrElse(return None)
          def unbuild(e: Expr): (Type, Expr, List[Identifier]) = e match {
            case ADTSelector(e, i) =>
              val (t, res, l) = unbuild(e)
              (t, res, l :+ i)
            case res => (tpe, res, Nil)
          }
          Some(unbuild(adtselectors))
        case _ => None
      }
    }
  }

  /** To build and extract a StringInsert specification. Works for modifications as well */
  object StringInsert extends Enumeration {
    private val leftName = "leftTreeStr"
    private val rightName = "rightTreeStr"
    type InsertDirection = Value
    val InsertToLeft, InsertToRight, InsertAutomatic = Value

    /** Need a preference to attach to left or right. If not specified, will try to infer it from the expressions
      * @param left The untouched string to the left of the insertion (may have removals)
      * @param s The newly inserted string
      * @param right The untouched string to the right of the insertion (may have removals)
      * @param direction -1 if the insertion should be inserted to left, 1 to right, 0 if automatically guessed.
      **/
    def apply(left: String, s: String, right: String, direction: InsertDirection): ProgramFormula = {
      val leftTreeStr = Variable(FreshIdentifier(leftName, true), StringType, Set())
      val rightTreeStr = Variable(FreshIdentifier(rightName, true), StringType, Set())
      val rDirection = if(direction != InsertAutomatic) direction else {
        val leftJump = ReverseProgram.StringConcatReverser.typeJump(left, s)
        val rightJump = ReverseProgram.StringConcatReverser.typeJump(s, right)
        if(leftJump < rightJump) {
          InsertToLeft
        } else {
          InsertToRight
        }
      }

      rDirection match {
        case InsertToLeft =>
          ProgramFormula(
            StringLiteral(left) +& StringLiteral(s) +& rightTreeStr,
            // tree === leftTreeStr +& rightTreeStr && (if not modificaiton)
            rightTreeStr === StringLiteral(right)
          )
        case InsertToRight =>
          ProgramFormula(
            leftTreeStr +& StringLiteral(s) +& StringLiteral(right),
            leftTreeStr === StringLiteral(left)
          )

      }

    }

    def unapply(f: ProgramFormula): Option[(String, String, String, InsertDirection)] = {
      f.expr match {
        case (StringLiteral(leftBefore)) +& StringLiteral(inserted) +& (rightTreeStr@Variable(idRight, StringType, _))
          if idRight.name == rightName
        =>
          val StringLiteral(rightBefore) = f.formula.findConstraintValue(rightTreeStr).getOrElse(return None)
          Some((leftBefore, inserted, rightBefore, InsertToLeft))
        case (leftTreeStr@Variable(idLeft, StringType, _)) +& StringLiteral(inserted) +& StringLiteral(rightBefore)
          if idLeft.name == leftName
        =>
          val StringLiteral(leftBefore) = f.formula.findConstraintValue(leftTreeStr).getOrElse(return None)
          Some((leftBefore, inserted, rightBefore, InsertToRight))
        case _ => None
      }
    }
  }

  object ListInsert {
    private val leftName = "leftTreeList"
    private val rightName = "rightTreeList"

    def apply(tpe: Type, leftUnmodified: List[Expr], inserted: List[Expr], rightUnmodified: List[Expr], remaining: Expr/* = BooleanLiteral(true)*/): ProgramFormula = {
      val leftTreeList  = Variable(FreshIdentifier(leftName,  true), T(Utils.list)(tpe), Set())
      val rightTreeList = Variable(FreshIdentifier(rightName, true), T(Utils.list)(tpe), Set())
      ProgramFormula(
        E(Utils.listconcat)(tpe)(E(Utils.listconcat)(tpe)(
          leftTreeList,
          ListLiteral(inserted, tpe)),
          rightTreeList),
        // tree === E(Utils.listconcat)(tpe)(leftTreeList, rightTreeList)
        leftTreeList === ListLiteral(leftUnmodified, tpe) && rightTreeList === ListLiteral(rightUnmodified, tpe)
      ) combineWith Formula(remaining)
    }

    def unapply(f: ProgramFormula): Option[(Type, List[Expr], List[Expr], List[Expr], Expr)] = {
      f.expr match {
        case FunctionInvocation(Utils.listconcat, Seq(tpe0), Seq(
        FunctionInvocation(Utils.listconcat, Seq(tpe1), Seq(
        leftTreeList@Variable(idLeft, ADTType(Utils.list, Seq(tpe2)), _),
        ListLiteral(inserted, tpe3))),
        (rightTreeList@Variable(idRight, ADTType(Utils.list, Seq(tpe4)), _))))
          if idLeft.name == leftName && idRight.name == rightName && tpe0 == tpe1 && tpe1 == tpe2 && tpe2 == tpe3 && tpe3 == tpe4
        =>
          val ListLiteral(leftBefore, _) = f.formula.findConstraintValue(leftTreeList).getOrElse(return None)
          val ListLiteral(rightBefore, _) = f.formula.findConstraintValue(rightTreeList).getOrElse(return None)
          val Formula(remaining) = f.formula.withoutFirstConstraintOn(leftTreeList).withoutFirstConstraintOn(rightTreeList)
          Some((tpe1, leftBefore, inserted, rightBefore, remaining))
        case _ => None
      }
    }
  }

  /** Inserts a variable for a given selected text.*/
  object CloneText {
    val leftName = "lClone"
    val rightName = "rClone"
    def apply(left: Expr, s: Expr, right: Expr): ProgramFormula = {
      val insertedVarName: String = s match {
        case StringLiteral(text) => text.split("\\W+").find(x => x.nonEmpty && x.charAt(0).isLetter).getOrElse("x")
        case _ => "x"
      }
      val insertedVar = Variable(FreshIdentifier(insertedVarName.toLowerCase()), StringType, Set())

      ProgramFormula(
        left +& insertedVar +& right,
        // tree === left +& s +& right &&    (if not modificaiton)
        insertedVar === s
      )
    }

    def unapply(f: ProgramFormula): Option[(String, String, String)] = {
      f.expr match {
        case StringLiteral(left) +& (v@Variable(id, StringType, _)) +& StringLiteral(right) =>
          f.formula.findConstraintValue(v).getOrElse(return None) match {
            case StringLiteral(cloned) =>
              Some((left, cloned, right))
            case _ => None
          }
        case _ => None
      }
    }
  }

  /** Paste a previously cloned variable. Like  StringInsert but with a variable inside it. */
  object PasteVariable {
    private val leftName = "lPaste"
    private val rightName = "rPaste"

    def apply(left: Expr, insertedVar: Variable, right: Expr): ProgramFormula = {
      ProgramFormula(
        left +& insertedVar +& right
      )
    }

    def unapply(f: ProgramFormula): Option[(String, Variable, String)] = {
      f.expr match {
        case StringLiteral(left) +& (v@Variable(id, StringType, _)) +& StringLiteral(right) =>
          f.formula.findConstraintValue(v).getOrElse(return None) match {
            case original: Variable =>
              Some((left, original, right))
            case _ => None
          }
        case _ => None
      }
    }
  }
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
}
