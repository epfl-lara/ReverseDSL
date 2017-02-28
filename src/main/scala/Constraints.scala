import ImplicitTuples._
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import inox.InoxProgram

object Utils {
  val list: Identifier = FreshIdentifier("List")
  val cons: Identifier = FreshIdentifier("Cons")
  val nil: Identifier = FreshIdentifier("Nil")
  val head: Identifier = FreshIdentifier("head")
  val tail: Identifier = FreshIdentifier("tail")
  val listSort = mkSort(list)("A")(Seq(cons, nil))
  val consConstructor = mkConstructor(cons)("A")(Some(list))( stp => Seq(ValDef(head, stp(0)), ValDef(tail, T(list)(stp(0)))))
  val nilConstructor = mkConstructor(nil)("A")(Some(list))( stp => Seq())

  val option: Identifier = FreshIdentifier("Option")
  val some: Identifier = FreshIdentifier("Some")
  val none: Identifier = FreshIdentifier("None")
  val optionSort = mkSort(option)("A")(Seq(some, none))
  val someConstructor = mkConstructor(some)("A")(Some(option))( stp => Seq(ValDef(value, stp(0))))
  val noneConstructor = mkConstructor(none)("A")(Some(option))( stp => Seq())

  val either: Identifier = FreshIdentifier("Either")
  val left: Identifier = FreshIdentifier("Left")
  val right: Identifier = FreshIdentifier("Right")
  val value: Identifier = FreshIdentifier("value")
  val eitherSort = mkSort(either)("A", "B")(Seq(left, right))
  val leftConstructor = mkConstructor(left)("A", "B")(Some(either))(stp => Seq(ValDef(value, stp(0))))
  val rightConstructor = mkConstructor(right)("A", "B")(Some(either))(stp => Seq(ValDef(value, stp(1))))

  val allConstructors = List(
    listSort,
    optionSort,
    eitherSort,
    consConstructor,
    nilConstructor,
    leftConstructor,
    rightConstructor,
    someConstructor,
    noneConstructor
  )
}

/** A type which can be converted to inox types, and whose expressions can be obtained from inox expressions */
trait Constrainable[A] { self =>
  type theType = A
  def getType: inox.trees.dsl.trees.Type
  def recoverFrom(e: Expr): A
  def produce(a: theType): Expr
}

/** Implicit helpers to build constrainable types.*/
object Constrainable {
  implicit object StringConstrainable extends Constrainable[String] {
    def getType = StringType
    def recoverFrom(e: Expr): String = e match {
      case StringLiteral(s) => s
      case _ => throw new Exception("Could not recover string from " + e)
    }
    def produce(a: String): inox.trees.Expr = E(a)
  }
  implicit object IntConstrainable extends Constrainable[Int] {
    def getType = Int32Type
    def recoverFrom(e: Expr): Int = e match {
      case IntLiteral(s) => s
      case _ => throw new Exception("Could not recover int from " + e)
    }
    def produce(a: Int): inox.trees.Expr = E(a)
  }

  def combine[A, B](self: Constrainable[A], other: Constrainable[B]): Constrainable[(A, B)] = new Constrainable[(A, B)] {
    def getType = T(tuple2)(self.getType, other.getType)
    def recoverFrom(e: Expr): (A, B) = e match {
      case ADT(_, Seq(a, b)) => (self.recoverFrom(a), other.recoverFrom(b))
      case _ => throw new Exception("Could not recover tuple from " + e)
    }
    def produce(a: (A, B)): Expr = ADT(ADTType(tuple2, Seq(self.getType, other.getType)), Seq(self.produce(a._1), other.produce(a._2)))
  }

  private def c[A : Constrainable] = implicitly[Constrainable[A]]

  implicit def tuple2Constrainable[A : Constrainable, B: Constrainable] : Constrainable[(A, B)] =
    combine(implicitly[Constrainable[A]], implicitly[Constrainable[B]])
  implicit def tuple3Constrainable[A : Constrainable, B: Constrainable, C: Constrainable] : Constrainable[(A, B, C)] =
    ImplicitTuples.Combination3[A, B, C](c[A], c[B], c[C])
  /*implicit def tuple4Constrainable[A : Constrainable, B: Constrainable, C: Constrainable, D: Constrainable]
  : Constrainable[(A, B, C, D)] =
    ImplicitTuples.Combination[(A, B, C, D)](c[A], c[B], c[C], c[D])*/
  //If need more tuples, add them here.

  implicit def listConstrainable[A: Constrainable]: Constrainable[List[A]] = new Constrainable[List[A]] {
    import Utils.{list, nil, cons}
    val underlying = implicitly[Constrainable[A]]
    def getType: inox.trees.dsl.trees.Type = T(list)(underlying.getType)

    def recoverFrom(e: inox.trees.Expr): List[A] = e match {
      case ADT(_, Seq(head, tail)) => underlying.recoverFrom(head) :: recoverFrom(tail)
      case ADT(_, Seq()) => Nil
      case _ => throw new Exception("Could not recover list from " + e)

    }

    def produce(a: List[A]): inox.trees.Expr = a match {
      case Nil => ADT(ADTType(nil, Seq(underlying.getType)), Seq())
      case head :: tail => ADT(ADTType(cons, Seq(underlying.getType)), Seq(underlying.produce(head), produce(tail)))
    }
  }

  implicit def optionConstrainable[A: Constrainable]: Constrainable[Option[A]] = new Constrainable[Option[A]] {
    import Utils.{option, some, none}
    val underlying = implicitly[Constrainable[A]]
    def getType: inox.trees.dsl.trees.Type = T(option)(underlying.getType)

    def recoverFrom(e: inox.trees.Expr): Option[A] = e match {
      case ADT(_, Seq(value)) => Some(underlying.recoverFrom(value))
      case ADT(_, Seq()) => None
      case _ => throw new Exception("Could not recover list from " + e)
    }

    def produce(a: Option[A]): inox.trees.Expr = a match {
      case None => ADT(ADTType(none, Seq(underlying.getType)), Seq())
      case Some(value) => ADT(ADTType(some, Seq(underlying.getType)), Seq(underlying.produce(value)))
    }
  }

  implicit def eitherConstrainable[A: Constrainable, B: Constrainable]: Constrainable[Either[A, B]] =
    new Constrainable[Either[A, B]] {
    import Utils.{either, left, right}
    def getType: inox.trees.dsl.trees.Type = T(either)(inoxTypeOf[A], inoxTypeOf[B])

    def recoverFrom(e: inox.trees.Expr): Either[A, B] = e match {
      case ADT(ADTType(`left`, _), Seq(value)) => Left(exprOfInox[A](value))
      case ADT(ADTType(`right`, _), Seq(value)) => Right(exprOfInox[B](value))
      case _ => throw new Exception("Could not recover either from " + e)
    }

    def produce(a: Either[A, B]): inox.trees.Expr = a match {
      case Left(value) =>   ADT(ADTType(left, Seq(inoxTypeOf[A], inoxTypeOf[B])), Seq(inoxExprOf[A](value)))
      case Right(value) =>  ADT(ADTType(right, Seq(inoxTypeOf[A], inoxTypeOf[B])), Seq(inoxExprOf[B](value)))
    }
  }

  /** Obtains the inox type of a given type. */
  def inoxTypeOf[A:Constrainable] = implicitly[Constrainable[A]].getType

  /** Creates a variable with the given name and type*/
  def variable[A:Constrainable](name: String, alwaysShowUniqueId: Boolean = false) =
    Variable(FreshIdentifier(name, alwaysShowUniqueId), inoxTypeOf[A], Set())

  /** Obtains the expression from an inox expression */
  def exprOfInox[A:Constrainable](e: inox.trees.Expr) = implicitly[Constrainable[A]].recoverFrom(e)

  /** Converts a value to an inox expression */
  def inoxExprOf[A: Constrainable](e: A) = implicitly[Constrainable[A]].produce(e)
}
import Constrainable._
/*
trait ConstraintInterface[A] {
  def toStream(solutionVar: inox.trees.Variable): Stream[A]
}

case class BridgeConstraint[A: Constrainable](left: ConstraintInterface[_], middleProblem: , right: ConstraintInterface[_]) extends ConstraintInterface[A] {

}*/

abstract class Tree[LeafValue, NodeValue]

case class Node[LeafValue, NodeValue](left: Tree[LeafValue, NodeValue], value: NodeValue, right: Tree[LeafValue, NodeValue]) extends Tree[LeafValue, NodeValue]
case class Leaf[LeafValue, NodeValue](value: LeafValue) extends Tree[LeafValue, NodeValue]

/** A wrapper around an inox Expr which can enumerate solutions*/
case class Constraint[A: Constrainable](private val formula: Expr,
                                        functions: Map[Identifier, ManualReverse[_, _]] = Map())/* extends ConstraintInterface[A]*/ {
  /** Adds a new assignment to this constraint */
  def apply[A: Constrainable](tuple: (inox.trees.Variable, A)) = this && tuple._1 === inoxExprOf[A](tuple._2)

  /** Adds a new conjunct to this constraint */
  def &&(b: Expr) = Constraint[A](formula && b, functions)

  /** Adds a new conjunct to this constraint */
  def &&[B: Constrainable](b: Constraint[B]) = Constraint[A](formula && b.formula, functions ++ b.functions)
  def <&&[B: Constrainable](b: Constraint[B]): Constraint[B] = Constraint[B](formula && b.formula, functions ++ b.functions)

  import inox.solvers._
  import SolverResponses._

  implicit val symbols = {
    NoSymbols
      .withFunctions(Seq())
      .withADTs(allTupleConstructors ++ Utils.allConstructors)
  }
  // The program
  lazy val context = Context.empty.copy(options = Options(Seq(optSelectedSolvers(Set("smt-cvc4")))))
  lazy val prog = InoxProgram(context, symbols)

  type ThisSolver = solvers.combinators.TimeoutSolver { val program: prog.type }

  /** Simplify the formula by replacing String method calls, removing equalities between identifiers */
  def simplify(solutionVar: Variable): Constraint[A] = {
    val assignments = {
      val TopLevelAnds(conjuncts) = formula
      conjuncts.collect{
        case Equals(v: Variable, t: Literal[_]) => (v -> t)
      }.toMap
    }

    object LeftConstant {
      def unapply(s: inox.trees.Expr): Some[(String, Option[inox.trees.Expr])] = Some(s match {
        case StringConcat(a, b) =>
          LeftConstant.unapply(a).get match {
            case (sa, Some(ea)) => (sa, Some(StringConcat(ea, b)))
            case (sa, None) =>
              LeftConstant.unapply(b).get match {
                case (sb, seb) => (sa + sb, seb)
              }
          }
        case StringLiteral(s) => (s, None)
        case v: Variable => assignments.get(v) match {
          case Some(StringLiteral(s)) => (s, None)
          case _ => ("", Some(v))
        }
        case e => ("", Some(e))
      })
    }

    object RightConstant {
      def unapply(s: inox.trees.Expr): Some[(Option[inox.trees.Expr], String)] = Some(s match {
        case StringConcat(a, b) =>
          RightConstant.unapply(b).get match {
            case (Some(eb), sb) => (Some(StringConcat(a, eb)), sb)
            case (None, sb) =>
              RightConstant.unapply(a).get match {
                case (sea, sa) => (sea, sa + sb)
              }
          }
        case StringLiteral(s) => (None, s)
        case v: Variable => assignments.get(v) match {
          case Some(StringLiteral(s)) => (None, s)
          case _ => (Some(v), "")
        }
        case e => (Some(e), "")
      })
    }

    val toplevelIdentityRemoved = (x: Expr) => x match {
      case TopLevelAnds(ands) =>
        val topEqualities = ands.collect{ case Equals(v1: Variable, v2: Variable) => (if(v1 != solutionVar) v1 -> v2 else v2 -> v1):(Expr, Expr) }
        inox.trees.exprOps.postMap(topEqualities.toMap.get)(x)
      case _ => x
    }
    //println("#2 " + toplevelIdentityRemoved)
    val removedAndTrue =
      inox.trees.exprOps.postMap{
        case And(exprs) =>
          val trueAnds = exprs.filterNot{ case BooleanLiteral(true) => true case Equals(v, v2) if v == v2 => true case _ => false }
          Some(if(trueAnds.isEmpty) E(true) else
          if(trueAnds.length == 1) trueAnds.head else
            And(trueAnds))
        case _ => None
      } _

    val removeFalseTrue =
      inox.trees.exprOps.postMap{
        case And(exprs) =>
          val isFalse = exprs.exists{
            case Equals(LeftConstant(a, ea), LeftConstant(b, eb)) if !a.startsWith(b) && !b.startsWith(a) => true
            case Equals(RightConstant(ea, a), RightConstant(eb, b)) if !a.endsWith(b) && !b.endsWith(a) => true
            case _ => false
          }
          if(isFalse) Some(BooleanLiteral(false)) else None
        case Or(exprs) =>
          val e = exprs.filter{
            case BooleanLiteral(false) => false
            case _ => true
          }
          Some(or(e: _*))
        case Not(BooleanLiteral(b)) => Some(BooleanLiteral(!b))
        case _ => None
      } _

    val finalFormula = (
                toplevelIdentityRemoved
        andThen removedAndTrue
        andThen removeFalseTrue
      )(formula)

    Constraint(finalFormula)
  }

  /** Returns a stream of solutions satisfying the constraint */
  def toStream(solutionVar: inox.trees.Variable): Stream[A] = {
    val simplified = simplify(solutionVar).formula

    //println("######## Converting this formula to stream of solutions ######\n" + simplified)

    // Convert the formula to a stream of conjuncts, each of one being able to yield solutions
    def getStreamOfConjuncts(e: Expr): Stream[Seq[Expr]] = {
      e match {
        case And(Seq(a1, a2)) => for {a <- getStreamOfConjuncts(a1); b <- getStreamOfConjuncts(a2); c = a ++ b} yield c
        case And(a1 +: at) => for {a <- getStreamOfConjuncts(a1); b <- getStreamOfConjuncts(And(at)); c = a ++ b} yield c
        case Or(exprs) => exprs.toStream.flatMap(getStreamOfConjuncts)
        case k => Stream(Seq(k))
      }
    }

    /** the leaf values are regular expressions, the node value are function conversions. */
    def splitAtUnknownFunctions(e: Seq[Expr]): Tree[Seq[Expr], Expr] = {
      val (left, valueAndRight) = e.span{
        case k@Equals(FunctionInvocation(identifier, Seq(), Seq(inId, inDefault)), _) if functions contains identifier => false
        case k@Equals(_, FunctionInvocation(identifier, Seq(), Seq(inId, inDefault))) if functions contains identifier => false
        case _ => true
      }
      if(valueAndRight.isEmpty) {
        Leaf(left)
      } else {
        val value +: right = valueAndRight
        if(right.isEmpty) throw new Exception("Could not find any value to recover the split at " + e)
        Node(Leaf(left), value, splitAtUnknownFunctions(right))
      }
    }

    // Separates the "Maybe(a == b)" statements from the conjunct
    def splitMaybe(e: Seq[Expr], notMaybes: Seq[Expr], maybes: Seq[Equals]): (List[Expr], List[Equals]) = {
      e match {
        case Seq() => (notMaybes.reverse.toList, maybes.reverse.toList)
        case FunctionInvocation(Common.maybe, _, Seq(equality@Equals(a, b))) +: tail =>
          splitMaybe(tail, notMaybes, equality +: maybes)
        case a +: tail =>
          splitMaybe(tail, a +: notMaybes, maybes)
      }
    }

    def addMaybes(e: (List[Expr], List[Equals]), startToDeleteAt: Int = 0): Stream[(ThisSolver, prog.Model)] = {
      /*
         If there are top-level constructs of the form ... && function(in, [inValue]) == out && ...
         and function is registered as manual reversing, we split the constraint into two constraints.
         A = all the conjuncts to the left of this expression (containing in)
         B = all the conjuncts to the right of this expression (containing out)
         We solve B and obtain model M
         We run putManual with the two given arguments to obtain a stream of in values.
         For each in value V, we solve the equations
         A && in == V && M
      */

      val solver = prog.getSolver.getNewSolver
      //println("solving " + and(e._1 ++ e._2 : _*))
      solver.assertCnstr(and(e._1 ++ e._2 : _*))
      //println("#2")
      solver.check(SolverResponses.Model) match {
        case SatWithModel(model) =>
          //println("One solution !")
          Stream((solver, model))
        case _ =>
          //println("No solution. Removing maybes...")
        for{i <- (startToDeleteAt until e._2.length).toStream
            seq = e._2.take(i) ++ e._2.drop(i+1)
            solver <- addMaybes((e._1, seq), i)
          } yield solver
      }
    }

    def getStreamOfSolutions(inputVar: Variable, e: (ThisSolver, prog.Model)): Stream[prog.Model] = {
      val solver = e._1
      val solutionInit = e._2
      //println(s"Looking for $inputVar in $solutionInit")
      val solutionInitExpr: Expr = solutionInit.vars(inputVar.toVal  : inox.trees.ValDef)
      //println("Found solution " + solutionInitExpr)
      //println("Supposing " + !(solutionVar === solutionInit))

      def otherSolutions(prevSol: inox.trees.Expr): Stream[prog.Model] = {
        solver.check(SolverResponses.Model) match {
          case SatWithModel(model) =>
            // We are going to plug in the maximum number of equals possible until it breaks.
            val solution: Expr = model.vars(solutionVar.toVal  : inox.trees.ValDef)
            //println("Found solution " + solution)
            if (prevSol == solution) Stream.empty else {
              model #:: {
                //println("Supposing " + !(solutionVar === solution))
                solver.assertCnstr(!(inputVar === solution))
                otherSolutions(solution)
              }
            }
          case _ =>
            //println("No more solutions")
            Stream.empty[prog.Model]
        }
      }
      solutionInit #:: {
        solver.assertCnstr(!(inputVar === solutionInitExpr))
        otherSolutions(solutionInitExpr)
      }
    }

    def solveTrees(t: Tree[Seq[Expr], Expr]): Stream[(ThisSolver, prog.Model)] = {
      t match {
        case Leaf(seqExpr) =>
          val x  = splitMaybe(seqExpr, Nil, Nil)
          for{ solver <- addMaybes(x, 0) } yield solver
        case Node(Leaf(seqExpr), value, right) =>
          //println("First we will solve " + right)
          //println("Then we inverse " + value)
          //println("And then we solve " + seqExpr)*
          val (function: ManualReverse[_, _], inVar, inDefault, outVar) = value match {
            case k@Equals(FunctionInvocation(identifier, Seq(), Seq(inVar: Variable, inDefault)), b: Variable) => (functions(identifier), inVar, inDefault, b)
            case k@Equals(b: Variable, FunctionInvocation(identifier, Seq(), Seq(inVar: Variable, inDefault))) => (functions(identifier), inVar, inDefault, b)
            case _ => throw new Exception("Cannot reverse this equality: " + value)
          }

          def getInValues[A, B](function: ManualReverse[A, B], outValue: Expr, inDefault: Expr): Iterable[Expr] = {
            val realOutValue = function.constrainableOutput.recoverFrom(outValue)
            val realDefaultValue = optionConstrainable(function.constrainableInput).recoverFrom(inDefault)
            val inValues = function.putManual(realOutValue, realDefaultValue)
            inValues.map(function.constrainableInput.produce)
          }

          for { solvermodel <- solveTrees(right)
                model <- getStreamOfSolutions(outVar, solvermodel)
                outValue = model.vars(outVar.toVal  : inox.trees.ValDef)
                inValue <- getInValues(function, outValue, inDefault)
                newSeqExpr = (seqExpr :+ Equals(inVar, inValue)) ++ model.vars.map{ case (v, e) => Equals(v.toVariable, e) }
                //_ = println("Solving this :" + newSeqExpr)
                x  = splitMaybe(newSeqExpr, Nil, Nil)
                //_ = println("Solving maybe:" + x)
                solver <- addMaybes(x, 0)
          } yield {
            solver
          }

        case _ => throw new Exception("[Internal error] Does not support this shape of tree : " + t)
      }
    }

    // The stream of conjuncts splitted with the maybes.
    for{ a <- getStreamOfConjuncts(simplified)
         splitted = splitAtUnknownFunctions(a)
         solver <- solveTrees(splitted)
         modelInox <- getStreamOfSolutions(solutionVar, solver)
         solutionInox = modelInox.vars(solutionVar.toVal: inox.trees.ValDef)
         solution = exprOfInox[A](solutionInox)
    }
      yield solution
  //println(streamOfConjuncts
  //implicit val po = PrinterOptions.fromContext(Context.empty)
  //println(symbols.explainTyping(streamOfConjuncts.head))
  }
}
