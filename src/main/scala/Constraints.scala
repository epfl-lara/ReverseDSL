

/*
trait Type

case object StringType extends Type
case object IntType extends Type
case object BooleanType extends Type
case object BigIntType extends Type
case class NamedType(definition: Symbol, targs: List[Type]) extends Type
case class LambdaType(args: List[Type], result: Type) extends Type

trait Definition
case class CaseClassDefinition(name: String, args: List[(Symbol, Type)], targs: List[Symbol], superClass: Option[NamedType] = None) extends Definition
case class AbstractClassDefinition(name: String, targs: List[Symbol], superClass: Option[NamedType] = None) extends Definition

case class SymbolTable(
  varTypes: Map[Symbol, Type],
  typeValues: Map[Symbol, Type],
  typeDefinitions: Map[Symbol, Definition])

trait Expr {
  def getType(implicit symbolTable: SymbolTable): Type
}

case class StringValue(value: String)   extends Expr { def getType(implicit symbolTable: SymbolTable) = StringType }
case class IntValue(value: Int)         extends Expr { def getType(implicit symbolTable: SymbolTable) = IntType }
case class BooleanValue(value: Boolean) extends Expr { def getType(implicit symbolTable: SymbolTable) = BooleanType }
case class BigIntValue(value: BigInt)   extends Expr { def getType(implicit symbolTable: SymbolTable) = BigIntType }
case class GenericValue(s: Symbol)      extends Expr {
  def getType(implicit symbolTable: SymbolTable) = symbolTable.varTypes(s)
}
case class LambdaValue(variables: List[(Symbol, Type)], body: Expr) extends Expr {
  def getType(implicit symbolTable: SymbolTable) = {
    val bodyType = body.getType(symbolTable.copy(varTypes = symbolTable.varTypes ++ variables))
    LambdaType(variables.map(v => TypeOps.instantiate(v._2, Map())), bodyType)
  }
}

object TypeOps {
  /*def expand(t: Type)(implicit symbolTable: SymbolTable) = t match {
    c
    case NamedType(s, targs) =>
      val targs2 = targs map expand
      symbolTable.typeDefinitions.get(symbol) match {
        case Some(definition) =>
        case None =>
      }
  }*/
  def instantiate(t: Type, m: Map[Symbol, Type])(implicit symbolTable: SymbolTable): Type = t match {
    case NamedType(d, Nil) => m.get(d) match {
      case Some(k) => instantiate(k, m)
      case None =>
        symbolTable.typeValues.get(d) match {
          case Some(k) => k
          case None => t
        }
      }
    case NamedType(d, targs) => NamedType(d, targs.map(instantiate(_, m)))
    case n => n
  }
  
  def parentsIncludingSymbol(tpe: Type)(implicit symbolTable: SymbolTable): List[Type] = {
    tpe +: ( tpe match {
      case NamedType(definition, targs) =>
         symbolTable.typeDefinitions.get(definition) match {
           case Some(CaseClassDefinition(_, _, targs2, Some(parent))) =>
             val instantiatedParent = instantiate(parent, targs2.zip(targs).toMap)
             parentsIncludingSymbol(instantiatedParent)
           case Some(AbstractClassDefinition(_, targs2, Some(parent))) =>
             val instantiatedParent = instantiate(parent, targs2.zip(targs).toMap)
             parentsIncludingSymbol(instantiatedParent)
           case _ => Nil
        }
      case _ => Nil
    }
     
    )
  }
  
  def leastUpperBound(def1: Type, def2: Type)(implicit symbolTable: SymbolTable): Option[Type] = {
    val pdef1 = parentsIncludingSymbol(def1)
    val pdef2 = parentsIncludingSymbol(def2)
    val (c, _) = pdef1.reverse.zip(pdef2.reverse).span(x => x._1 == x._2)
    c.lastOption.map(_._1)
  }
  
  // Incomplete Hindley milner inference (needs an abstract-concrete table)
  def unify(t: List[(Type, Type)])(implicit symbolTable: SymbolTable): Map[Symbol, Type] = t match {
    case Nil => Map()
    case (a, b)::tail if a == b => unify(tail)
    case (a@NamedType(definition, targs), b@NamedType(definition2, targs2))::tail =>
      leastUpperBound(a, b) match {
        case Some(definitionUpper) =>
          val argumentUnification = unify(targs.zip(targs2))
          argumentUnification ++ unify(tail)(symbolTable.copy(typeValues = symbolTable.typeValues ++ argumentUnification))
        case None => throw new Exception("Failed to unify the types $a and $b because they do not have the same definition.")
      }
    case (a@LambdaType(targs, result), b@LambdaType(targs2, result2))::tail =>
      val argumentUnification = unify(targs.zip(targs2))
      val newTypeValues = symbolTable.typeValues ++ argumentUnification
      val resultUnification = unify(List((result, result2)))(symbolTable.copy(typeValues = newTypeValues))
      val newSymbolTable2 = newTypeValues ++ resultUnification
      argumentUnification ++ resultUnification ++ unify(tail)(symbolTable.copy(typeValues = newSymbolTable2))
    case (a@NamedType(definition, Nil), b)::tail =>
      (symbolTable.typeDefinitions get definition) match {
        case None =>
          val newDef = symbolTable.typeValues.get(definition) match {
            case Some(x) if x == b => Nil
            case Some(x) => throw new Error(s"Could not merge types $x and $b with $a")
            case None => List(definition -> b)
          }
          val newTypeValues =  symbolTable.typeValues ++ newDef
          unify(tail)(symbolTable.copy(typeValues = newTypeValues)) ++ newDef
        case Some(t) =>throw new Error(s"Could not merge types $a (definition $t) and $b")
      }
    case (b, a@NamedType(definition, Nil))::tail =>
      unify((a, b)::tail)
    case (a, b)::tail => throw new Error(s"Could not merge types $a and $b")
  }
}

case class Select(s: Expr, e: Symbol) {
  def getType(implicit symbolTable: SymbolTable) = s.getType match {
    case NamedType(definition, targs) => symbolTable.typeDefinitions.get(definition) match {
      case Some(CaseClassDefinition(_, args, targsVars, _)) =>
        args.find(_._1 == e) match {
          case Some((_, tpe)) => TypeOps.instantiate(tpe, targsVars.zip(targs).toMap)
          case None if e == '== || e == '$eq$eq =>
            
          case _ => throw new Exception(s"could not find type $e in fields of $definition: $args")
        }
      case Some(a@AbstractClassDefinition(_, targs, _)) =>
        throw new Exception(s"Cannot select a field of abstract class $a")
      case None => throw new Exception(s"Could not find a type definition for $definition")
      case Some(a) => throw new Exception(s"Cannot select a field $e of $a")
    }
    case a => throw new Exception(s"Cannot select a field $e of $a") 
  }
}
case class Apply(s: Expr, l: List[Expr]) {
  def getType(implicit symbolTable: SymbolTable) = s.getType match {
    case LambdaType(argsTypes, resultType) =>
      val mapping = TypeOps.unify(l.map(_.getType).zip(argsTypes))
      TypeOps.instantiate(resultType, mapping)
    case t => throw new Exception(s"Cannot apply $s to $l because $s types to $t and not a lambda") 
  }
}

object Custom {
  val ta = NamedType('A, Nil) //'
  val tb = NamedType('B, Nil) //'
  val tc = NamedType('C, Nil) //'
  val td = NamedType('D, Nil) //'
  
  val libraryDefinition: Map[Symbol, Definition] = Map(
    'Tuple2 -> CaseClassDefinition("", List(('_1, ta), ('_2, tb)), List('A, 'B)), //'
    'Tuple3 -> CaseClassDefinition("", List(('_1, ta), ('_2, tb), ('_3, tc)), List('A, 'B, 'C)), //'
    'Tuple4 -> CaseClassDefinition("", List(('_1, ta), ('_2, tb), ('_3, tc), ('_4, td)), List('A, 'B, 'C, 'D)), //'
    //...
    'List -> AbstractClassDefinition("List", List('A)), //'
    'Nil -> CaseClassDefinition("Nil", List(), List('A), Some(NamedType('List, List(NamedType('A, Nil))))),  //'
    'Cons -> CaseClassDefinition("Cons", List(('head, ta), ('tail, NamedType('List, List(ta)))), List('A), Some(NamedType('List, List(NamedType('A, Nil))))) //'
  )
}*/

/*
case class MemberOfConstraint[A](orderedSet: List[A]) extends Constraint[A] {
  def foreach[U](f: A => U) = orderedSet.foreach(f)
}

case class MemberOfLazyConstraint[A](orderedSet: Stream[A]) extends Constraint[A] {
  def foreach[U](f: A => U) = orderedSet.foreach(f)
}*/

import ImplicitTuples._
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._

object Utils {
  val list: Identifier = FreshIdentifier("List")
  val cons: Identifier = FreshIdentifier("Cons")
  val nil: Identifier = FreshIdentifier("Nil")

  val head: Identifier = FreshIdentifier("head")
  val tail: Identifier = FreshIdentifier("tail")
}


trait Constrainable[A] { self =>
  def getType: inox.trees.dsl.trees.Type
  def zipWith[B](other: Constrainable[B]): Constrainable[(A, B)] = new Constrainable[(A, B)] {
    def getType = T(tuple2)(self.getType, other.getType)
    def recoverFrom(e: Expr): (A, B) = e match {
      case ADT(_, Seq(a, b)) => (self.recoverFrom(a), other.recoverFrom(b))
      case _ => throw new Exception("Could not recover tuple from " + e)
    }
  }
  def recoverFrom(e: Expr): A
}

object Constrainable {

  implicit object StringConstrainable extends Constrainable[String] {
    def getType = StringType

    override def recoverFrom(e: Expr): String = e match {
      case StringLiteral(s) => s
      case _ => throw new Exception("Could not recover string from " + e)
    }
  }
  implicit val StringStringConstrainable = StringConstrainable.zipWith(StringConstrainable)

  implicit def tupleConstrainable[A : Constrainable, B: Constrainable] : Constrainable[(A, B)] = implicitly[Constrainable[A]].zipWith(implicitly[Constrainable[B]])

  def getType[A:Constrainable] = implicitly[Constrainable[A]].getType
}
import Constrainable._

case class Constraint[A: Constrainable](formula: Expr) {
  def apply(tuple: (inox.trees.Variable, String)) = this && tuple._1 === E(tuple._2)

  def &&(b: Expr) = Constraint[A](formula && b)

  import inox.solvers._
  import SolverResponses._

  implicit val symbols = {
    NoSymbols
      .withFunctions(Seq())
      .withADTs(allTupleConstructors)
  }
  def tostream(solutionVar: Variable): Stream[A] = {
    // * step: We replace  c = remove(a, b) by (= (+ b c) a)
    // * step: We convert all maybe(a) to a || true
    // * step: We consider all top-level conjuncts of the for Identifier = Identifier and remove one of the two identifiers.
    // * step: We take the streamed CNF version of the formula
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
    }(formula)
    val toplevelIdentityRemoved = StringExprsMaybeReplaced match {
      case TopLevelAnds(ands) =>
        val topEqualities = ands.collect{ case Equals(v1, v2) => (if(v1 != solutionVar) v1 -> v2 else v2 -> v1):(Expr, Expr) }
        inox.trees.exprOps.postMap(topEqualities.toMap.get)(StringExprsMaybeReplaced)
      case _ => StringExprsMaybeReplaced
    }
    val removedAndTrue =
      inox.trees.exprOps.postMap{
        case And(exprs) =>
          val trueAnds = exprs.filterNot{ case BooleanLiteral(true) => true case Equals(v, v2) if v == v2 => true case _ => false }
          Some(if(trueAnds.isEmpty) E(true) else
          if(trueAnds.length == 1) trueAnds.head else
          And(trueAnds))
        case _ => None
      }(toplevelIdentityRemoved)
    def getStreamOfConjuncts(e: Expr): Stream[Seq[Expr]] = {
      e match {
        case And(Seq(a1, a2)) => for{ a <- getStreamOfConjuncts(a1); b <- getStreamOfConjuncts(a2) ; c = a ++ b } yield c
        case And(a1 +: at) => for{ a <- getStreamOfConjuncts(a1); b <- getStreamOfConjuncts(And(at)) ; c = a ++ b } yield c
        case Or(exprs) => exprs.toStream.flatMap(getStreamOfConjuncts)
        case k => Stream(Seq(k))
      }
    }
    def expandMaybe(e: Seq[Expr]): Stream[Seq[Expr]] = {
      // If the LHS of a maybe is nowhere else, we keep it.
      // If the LHS of a maybe is somewhere else, we keep all of them, then one less, until there is at least one of them.
      e match {
        case Seq() => Stream(Seq())
        case FunctionInvocation(Common.maybe, _, Seq(equality@Equals(a, b))) +: tail =>
          if(!tail.exists((f: Expr) => f match {
            case FunctionInvocation(Common.maybe,  _, Seq(Equals(c, d))) => c == a
            case _ => false
          })) {
            expandMaybe(tail).map(equality +: _)
          } else { // There exists another one later.
            val tailFiltered = tail.filterNot{
              case FunctionInvocation(Common.maybe, _, Seq(Equals(c, d))) => c == a
              case _ => false
            }
            expandMaybe(tailFiltered).map(equality +: _) #::: expandMaybe(tail)
          }
        case head +: tail => expandMaybe(tail).map(head +: _)
      }

    }
    val streamOfConjuncts = getStreamOfConjuncts(removedAndTrue).flatMap(expandMaybe).map(And.apply)
    val program = InoxProgram(Context.empty, symbols)
    def getStreamOfSolutions(e: Expr): Stream[A] = {
      val solver = program.getSolver.getNewSolver
      solver.assertCnstr(e)
      var solving = e
      println("New solving")
      var prevSol: Option[Expr] = None
      def iterate(): Stream[A] = {
        println("Solving " + solving)
        solver.check(SolverResponses.Model) match {
          case SatWithModel(model) =>
            val solution: Expr = model.vars(solutionVar.toVal)
            if (prevSol.map(_ == solution).getOrElse(false)) Stream.empty else {
              prevSol = Some(solution)
              implicitly[Constrainable[A]].recoverFrom(solution) #:: {
                solving = solving && !(solutionVar === solution)
                solver.assertCnstr(!(solutionVar === solution))
                iterate()
              }
            }
          case _ => Stream.empty[A]
        }
      }
      iterate()
    }
  //  println(streamOfConjuncts
  //  implicit val po = PrinterOptions.fromContext(Context.empty)
//    println(symbols.explainTyping(streamOfConjuncts.head))

    streamOfConjuncts.flatMap(getStreamOfSolutions)
/*
    val solver = program.getSolver.getNewSolver
    solver.assertCnstr(streamOfConjuncts.head)
    println(solver.check(SolverResponses.Model))
    ???*/
  }
}
