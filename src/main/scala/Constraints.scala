

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

trait Constraint[A] extends Traversable[A] {
}
/*
case class MemberOfConstraint[A](orderedSet: List[A]) extends Constraint[A] {
  def foreach[U](f: A => U) = orderedSet.foreach(f)
}

case class MemberOfLazyConstraint[A](orderedSet: Stream[A]) extends Constraint[A] {
  def foreach[U](f: A => U) = orderedSet.foreach(f)
}*/

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

case class FormulaBasedConstraint[A](formula: Expr) extends Constraint[A] {
  def foreach[U](f: A => U) = {
    Nil
  }
  def intersectWith(other: Constraint[A]) = {
    
  }
}
