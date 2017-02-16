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
}

/** A type which can be converted to inox types, and whose expressions can be obtained from inox expressions */
trait Constrainable[A] { self =>
  def getType: inox.trees.dsl.trees.Type
  def recoverFrom(e: Expr): A
  def produce(a: A): Expr
  def zipWith[B](other: Constrainable[B]): Constrainable[(A, B)] = new Constrainable[(A, B)] {
    def getType = T(tuple2)(self.getType, other.getType)
    def recoverFrom(e: Expr): (A, B) = e match {
      case ADT(_, Seq(a, b)) => (self.recoverFrom(a), other.recoverFrom(b))
      case _ => throw new Exception("Could not recover tuple from " + e)
    }
    def produce(a: (A, B)): Expr = ADT(ADTType(tuple2, Seq(self.getType, other.getType)), Seq(self.produce(a._1), other.produce(a._2)))
  }
}

/** Implicit helpers to build constrainable types.*/
object Constrainable {
  implicit object StringConstrainable extends Constrainable[String] {
    def getType = StringType

    override def recoverFrom(e: Expr): String = e match {
      case StringLiteral(s) => s
      case _ => throw new Exception("Could not recover string from " + e)
    }

    override def produce(a: String): inox.trees.Expr = E(a)
  }
  implicit object IntConstrainable extends Constrainable[Int] {
    def getType = Int32Type

    override def recoverFrom(e: Expr): Int = e match {
      case IntLiteral(s) => s
      case _ => throw new Exception("Could not recover int from " + e)
    }

    override def produce(a: Int): inox.trees.Expr = E(a)
  }
  implicit val StringStringConstrainable = StringConstrainable.zipWith(StringConstrainable)

  implicit def tupleConstrainable[A : Constrainable, B: Constrainable] : Constrainable[(A, B)] = implicitly[Constrainable[A]].zipWith(implicitly[Constrainable[B]])

  /** Obtains the inox type of a given type. */
  def getType[A:Constrainable] = implicitly[Constrainable[A]].getType

  /** Creates a variable with the given name and type*/
  def variable[A:Constrainable](name: String, alwaysShowUniqueId: Boolean = false) =
    Variable(FreshIdentifier(name, alwaysShowUniqueId), getType[A], Set())

  /** Obtains the expression from an inox expression */
  def getExpr[A:Constrainable](e: inox.trees.Expr) = implicitly[Constrainable[A]].recoverFrom(e)

  /** Converts a value to an inox expression */
  def toExpr[A: Constrainable](e: A) = implicitly[Constrainable[A]].produce(e)
}
import Constrainable._

/** A wrapper around an inox Expr which can enumerate solutions*/
case class Constraint[A: Constrainable](formula: Expr) {
  /** Adds a new assignment to this constraint */
  def apply[A: Constrainable](tuple: (inox.trees.Variable, A)) = this && tuple._1 === toExpr[A](tuple._2)

  /** Adds a new conjunct to this constraint */
  def &&(b: Expr) = Constraint[A](formula && b)

  import inox.solvers._
  import SolverResponses._

  implicit val symbols = {
    NoSymbols
      .withFunctions(Seq())
      .withADTs(allTupleConstructors)
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

    val StringExprsMaybeReplaced = inox.trees.exprOps.postMap {
      case Equals(c, FunctionInvocation(StringAppendReverse.removeStart, _, Seq(a, b))) =>
        Some(Equals(a, StringConcat(b, c)))
      case Equals(FunctionInvocation(StringAppendReverse.removeStart, _, Seq(a, b)), c) =>
        Some(Equals(a, StringConcat(b, c)))
      case Equals(c, FunctionInvocation(StringAppendReverse.removeEnd, _, Seq(a, b))) =>
        Some(Equals(a, StringConcat(c, b)))
      case Equals(FunctionInvocation(StringAppendReverse.removeEnd, _, Seq(a, b)), c) =>
        Some(Equals(a, StringConcat(c, b)))
      case _ => None
    } _

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

    val finalFormula = (StringExprsMaybeReplaced
        andThen toplevelIdentityRemoved
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
        case And(Seq(a1, a2)) => for{ a <- getStreamOfConjuncts(a1); b <- getStreamOfConjuncts(a2) ; c = a ++ b } yield c
        case And(a1 +: at) => for{ a <- getStreamOfConjuncts(a1); b <- getStreamOfConjuncts(And(at)) ; c = a ++ b } yield c
        case Or(exprs) => exprs.toStream.flatMap(getStreamOfConjuncts)
        case k => Stream(Seq(k))
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

    // The stream of conjuncts splitted with the maybes.
    val streamOfConjuncts = getStreamOfConjuncts(simplified).map(x => splitMaybe(x, Nil, Nil))

    def addMaybes(e: (List[Expr], List[Equals]), startToDeleteAt: Int = 0): Stream[(ThisSolver, prog.Model)] = {
      val solver = prog.getSolver.getNewSolver
      //println("solving " + and(e._1 ++ e._2 : _*))
      solver.assertCnstr(and(e._1 ++ e._2 : _*))
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

    def getStreamOfSolutions(e: (ThisSolver, prog.Model)): Stream[A] = {
      val solver = e._1
      val solutionInit = e._2.vars(solutionVar.toVal : inox.trees.ValDef)
      val solutionInitExpr = getExpr[A](solutionInit)
      //println("Found solution " + solutionInit)
      //println("Supposing " + !(solutionVar === solutionInit))
      solver.assertCnstr(!(solutionVar === solutionInit))
      def otherSolutions(prevSol: inox.trees.Expr): Stream[A] = {
        solver.check(SolverResponses.Model) match {
          case SatWithModel(model) =>
            // We are going to plug in the maximum number of equals possible until it breaks.
            val solution: Expr = model.vars(solutionVar.toVal  : inox.trees.ValDef)
            //println("Found solution " + solution)
            if (prevSol == solution) Stream.empty else {
              getExpr[A](solution) #:: {
                //println("Supposing " + !(solutionVar === solution))
                solver.assertCnstr(!(solutionVar === solution))
                otherSolutions(solution)
              }
            }
          case _ =>
            //println("No more solutions")
            Stream.empty[A]
        }
      }
      solutionInitExpr #:: otherSolutions(solutionInit)
    }
  //println(streamOfConjuncts
  //implicit val po = PrinterOptions.fromContext(Context.empty)
  //println(symbols.explainTyping(streamOfConjuncts.head))

    for{ x <- streamOfConjuncts
         solver <- addMaybes(x, 0)
         solution <- getStreamOfSolutions(solver) } yield solution
  }
}
