import ImplicitTuples._
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import inox.InoxProgram

import scala.xml.MetaData

object Utils {
  /** Inner variables first */
  val value: Identifier = FreshIdentifier("value")
  val head: Identifier = FreshIdentifier("head")
  val tail: Identifier = FreshIdentifier("tail")
  val inner: Identifier = FreshIdentifier("inner")
  val text: Identifier = FreshIdentifier("text")
  val tag: Identifier = FreshIdentifier("tag")
  val children: Identifier = FreshIdentifier("children")
  val attributes: Identifier = FreshIdentifier("attributes")
  val styles: Identifier = FreshIdentifier("styles")
  val name: Identifier = FreshIdentifier("name")


  val list: Identifier = FreshIdentifier("List")
  val cons: Identifier = FreshIdentifier("Cons")
  val nil: Identifier = FreshIdentifier("Nil")
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
  val eitherSort = mkSort(either)("A", "B")(Seq(left, right))
  val leftConstructor = mkConstructor(left)("A", "B")(Some(either))(stp => Seq(ValDef(value, stp(0))))
  val rightConstructor = mkConstructor(right)("A", "B")(Some(either))(stp => Seq(ValDef(value, stp(1))))

  val xmlNode: Identifier = FreshIdentifier("Node")
  val xmlAttribute: Identifier = FreshIdentifier("Attribute")

  val webTree: Identifier = FreshIdentifier("WebTree")
  val webElement: Identifier = FreshIdentifier("WebElement")
  val innerWebElement: Identifier = FreshIdentifier("InnerWebElement")
  val textNode: Identifier = FreshIdentifier("TextNode")
  val element: Identifier = FreshIdentifier("Element")
  val webAttribute: Identifier = FreshIdentifier("WebAttribute")
  val webStyle: Identifier = FreshIdentifier("WebStyle")
  val webTreeSort = mkSort(webTree)()(Seq(webElement, webAttribute, webStyle))
  val innerWebElementSort = mkSort(innerWebElement)()(Seq(textNode, element))
  var webElementConstructor = mkConstructor(webElement)()(Some(webTree))(stp => Seq(ValDef(inner, T(innerWebElement)())))
  val textNodeConstructor = mkConstructor(textNode)()(Some(innerWebElement))(stp => Seq(ValDef(text, StringType)))
  val elementConstructor = mkConstructor(element)()(Some(innerWebElement))(stp =>
    Seq(ValDef(tag, StringType),
        ValDef(children, T(list)(T(webElement)())),
        ValDef(attributes, T(list)(T(webAttribute)())),
        ValDef(styles, T(list)(T(webStyle)()))))
  val webAttributeConstructor = mkConstructor(webAttribute)()(Some(webTree))(_ => Seq(
        ValDef(name, StringType),
        ValDef(value, StringType)))
  val webStyleConstructor = mkConstructor(webStyle)()(Some(webTree))(_ => Seq(
    ValDef(name, StringType),
    ValDef(value, StringType)))

  val xmlNodeConstructor = mkConstructor(xmlNode)()(None)(stp =>
    Seq(ValDef(tag, StringType),
      ValDef(attributes, T(list)(T(xmlAttribute)())),
      ValDef(children, T(list)(T(xmlNode)()))))

  val xmlAttributeConstructor = mkConstructor(xmlAttribute)()(None)(_ => Seq(
    ValDef(name, StringType),
    ValDef(value, StringType)))

  val allConstructors = List(
    listSort,
    consConstructor,
    nilConstructor,
    eitherSort,
    leftConstructor,
    rightConstructor,
    optionSort,
    someConstructor,
    noneConstructor,
    webTreeSort,
    innerWebElementSort,
    webElementConstructor,
    textNodeConstructor,
    elementConstructor,
    webAttributeConstructor,
    webStyleConstructor,
    xmlNodeConstructor,
    xmlAttributeConstructor
  )

  val filter = FreshIdentifier("filter")

  val defaultSymbols =
    NoSymbols.withADTs(allConstructors)
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

  private def c[A : Constrainable] = implicitly[Constrainable[A]]

  implicit def tuple2Constrainable[A : Constrainable, B: Constrainable] : Constrainable[(A, B)] =
    ImplicitTuples.Combination2(c[A], c[B])
  implicit def tuple3Constrainable[A : Constrainable, B: Constrainable, C: Constrainable] : Constrainable[(A, B, C)] =
    ImplicitTuples.Combination3(c[A], c[B], c[C])
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

  import WebTrees._

  implicit val WebTreeConstrainable: Constrainable[WebTree] = new  Constrainable[WebTree] {
    import Utils._
    def getType: inox.trees.dsl.trees.Type = T(webTree)()
    def produce(a: WebTree): inox.trees.Expr = a match {
      case a: WebElement => WebElementConstrainable.produce(a)
      case a: WebAttribute => WebAttributeConstrainable.produce(a)
      case a: WebStyle => WebStyleConstrainable.produce(a)
    }
    def recoverFrom(e: inox.trees.Expr): WebTree = e match {
      case ADT(ADTType(`webAttribute`, Seq()), _) => WebAttributeConstrainable.recoverFrom(e)
      case ADT(ADTType(`webStyle`, Seq()), _) => WebStyleConstrainable.recoverFrom(e)
      case e => WebElementConstrainable.recoverFrom(e)
    }
  }
  
  implicit val WebElementConstrainable: Constrainable[WebElement] = new  Constrainable[WebElement] {
    import Utils._
    def getType: inox.trees.dsl.trees.Type = T(webElement)()
    def produce(a: WebElement): inox.trees.Expr =
      ADT(ADTType(webElement, Seq()), Seq(InnerWebElementConstrainable.produce(a.inner)))
    def recoverFrom(e: inox.trees.Expr): WebElement = e match {
      case ADT(ADTType(webElement, Seq()), Seq(arg)) => WebElement(InnerWebElementConstrainable.recoverFrom(arg))
      case _ => throw new Exception("Could not recover WebElement from " + e)
    }
  }

  implicit val InnerWebElementConstrainable: Constrainable[InnerWebElement] = new  Constrainable[InnerWebElement] {
    import Utils._
    def getType: inox.trees.dsl.trees.Type = T(innerWebElement)()
    def produce(a: InnerWebElement): inox.trees.Expr = a match {
      case a: TextNode => TextNodeConstrainable.produce(a)
      case a: Element =>  ElementConstrainable.produce(a)
    }
    def recoverFrom(e: inox.trees.Expr): InnerWebElement = e match {
      case ADT(ADTType(`textNode`, Seq()), _) => TextNodeConstrainable.recoverFrom(e)
      case ADT(ADTType(`element`, Seq()), _) => ElementConstrainable.recoverFrom(e)
      case _ => throw new Exception("Could not recover InnerWebElement from " + e)
    }
  }

  implicit val TextNodeConstrainable: Constrainable[TextNode] = new Constrainable[TextNode] {
    import Utils._
    def getType: inox.trees.dsl.trees.Type = T(textNode)()
    def produce(a: TextNode): inox.trees.Expr = a match {
      case TextNode(s) => ADT(ADTType(textNode, Seq()), Seq(inoxExprOf[String](s)))
    }
    def recoverFrom(e: inox.trees.Expr): TextNode = e match {
      case ADT(ADTType(`textNode`, Seq()), Seq(s)) => TextNode(exprOfInox[String](s))
      case _ => throw new Exception("Could not recover TextNode from " + e)
    }
  }

  implicit val ElementConstrainable: Constrainable[Element] = new  Constrainable[Element] {
    import Utils._
    def getType: inox.trees.dsl.trees.Type = T(element)()
    def produce(a: Element): inox.trees.Expr = a match {
      case Element(tag, children, attributes, styles) => ADT(ADTType(element, Seq()),
        Seq(inoxExprOf[String](tag), inoxExprOf[List[WebElement]](children), inoxExprOf[List[WebAttribute]](attributes), inoxExprOf[List[WebStyle]](styles)))
    }
    def recoverFrom(e: inox.trees.Expr): Element = e match {
      case ADT(ADTType(`element`, Seq()), Seq(tag, children, attributes, styles)) =>
        Element(exprOfInox[String](tag), exprOfInox[List[WebElement]](children), exprOfInox[List[WebAttribute]](attributes), exprOfInox[List[WebStyle]](styles))
      case _ => throw new Exception("Could not recover Element from " + e)
    }
  }

  implicit val WebAttributeConstrainable: Constrainable[WebAttribute] = new  Constrainable[WebAttribute] {
    import Utils._
    def getType: inox.trees.dsl.trees.Type = T(webAttribute)()
    def produce(a: WebAttribute): inox.trees.Expr = a match {
      case WebAttribute(name, value) => ADT(ADTType(webAttribute, Seq()),
        Seq(inoxExprOf[String](name), inoxExprOf[String](value)))
    }
    def recoverFrom(e: inox.trees.Expr): WebAttribute = e match {
      case ADT(ADTType(`webAttribute`, Seq()), Seq(name, value)) =>
        WebAttribute(exprOfInox[String](name), exprOfInox[String](value))
      case _ => throw new Exception("Could not recover Element from " + e)
    }
  }

  implicit val WebStyleConstrainable: Constrainable[WebStyle] = new  Constrainable[WebStyle] {
    import Utils._
    def getType: inox.trees.dsl.trees.Type = T(webStyle)()
    def produce(a: WebStyle): inox.trees.Expr = a match {
      case WebStyle(name, value) => ADT(ADTType(webStyle, Seq()),
        Seq(inoxExprOf[String](name), inoxExprOf[String](value)))
    }
    def recoverFrom(e: inox.trees.Expr): WebStyle = e match {
      case ADT(ADTType(`webStyle`, Seq()), Seq(name, value)) =>
        WebStyle(exprOfInox[String](name), exprOfInox[String](value))
      case _ => throw new Exception("Could not recover Element from " + e)
    }
  }

  implicit val UnitConstrainable: Constrainable[Unit] = new Constrainable[Unit] {
    def getType = UnitType
    def produce(a: Unit) = UnitLiteral()
    def recoverFrom(e: inox.trees.Expr): Unit = ()
  }

  implicit val XMLConstrainable: Constrainable[XmlTrees.Node] = new Constrainable[XmlTrees.Node] {
    import Utils._
    def getType = T(xmlNode)()
    def produce(a: XmlTrees.Node): inox.trees.Expr = a match {
      case XmlTrees.Node(tag, attrs, children) =>
        ADT(ADTType(xmlNode, Seq()),
          Seq(inoxExprOf[String](tag), inoxExprOf[List[XmlTrees.XMLAttribute]](attrs), inoxExprOf[List[XmlTrees.Node]](children)))
    }
    def recoverFrom(e: inox.trees.Expr): XmlTrees.Node = e match {
      case ADT(ADTType(`xmlNode`, Seq()), Seq(tag, attributes, children)) =>
        XmlTrees.Node(exprOfInox[String](tag), exprOfInox[List[XmlTrees.XMLAttribute]](attributes), exprOfInox[List[XmlTrees.Node]](children))
      case _ => throw new Exception("Could not recover XmlTrees.Node from " + e)
    }
  }

  implicit val XMLAttributeConstrainable: Constrainable[XmlTrees.XMLAttribute] = new  Constrainable[XmlTrees.XMLAttribute] {
    import Utils._
    def getType: inox.trees.dsl.trees.Type = T(xmlAttribute)()
    def produce(a: XmlTrees.XMLAttribute): inox.trees.Expr = a match {
      case XmlTrees.XMLAttribute(name, value) => ADT(ADTType(xmlAttribute, Seq()),
        Seq(inoxExprOf[String](name), inoxExprOf[String](value)))
    }
    def recoverFrom(e: inox.trees.Expr): XmlTrees.XMLAttribute = e match {
      case ADT(ADTType(`xmlAttribute`, Seq()), Seq(name, value)) =>
        XmlTrees.XMLAttribute(exprOfInox[String](name), exprOfInox[String](value))
      case _ => throw new Exception("Could not recover XmlTrees.XMLAttribute from " + e)
    }
  }

  implicit def scalaNodeToXmlNode(node: scala.xml.Node): XmlTrees.Node = node match {
    case scala.xml.Text(text) =>
      XmlTrees.Node(text.trim(), List(), List())
    case n: scala.xml.Node =>
      val (tag, attributes, children) = scala.xml.Node.unapplySeq(n).get
      XmlTrees.Node(tag, scalaAttributesToXmlAttribute(attributes), children.toList.map(scalaNodeToXmlNode _).filter{
        case XmlTrees.Node(s, _, _) if s == "" => false
        case _ => true
      })
    case e =>
      println(e.getClass.getDeclaredMethods.mkString("\n"))
      throw new Exception(s"Could not match $e of class ${e.getClass}")
  }

  implicit def scalaAttributesToXmlAttribute(m: MetaData): List[XmlTrees.XMLAttribute] = {
    m.asAttrMap.toList.map{ case (key, value) => XmlTrees.XMLAttribute(key, value) }
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


  // Helper for building ADTs
  def _Cons[A: Constrainable](head: Expr, tail: Expr) = ADT(ADTType(Utils.cons, Seq(inoxTypeOf[A])), Seq(head, tail))
  def _Nil[A: Constrainable] = ADT(ADTType(Utils.nil, Seq(inoxTypeOf[A])), Seq())
  def _List[A: Constrainable](elements: Expr*): Expr = elements match {
    case Nil => _Nil[A]
    case head +: tail => _Cons[A](head, _List[A](tail: _*))
  }
  def _TextNode(value: Expr) = ADT(ADTType(Utils.textNode, Seq()), Seq(value))
  def _Element(tag: Expr, children: Expr, attributes: Expr, styles: Expr) =
    ADT(ADTType(Utils.element, Seq()), Seq(tag, children, attributes, styles))
  def _WebElement(inner: Expr) = ADT(ADTType(Utils.webElement, Seq()), Seq(inner))
  def _WebAttribute(key: Expr, value: Expr) = ADT(ADTType(Utils.webAttribute, Seq()), Seq(key, value))
  def _WebStyle(key: Expr, value: Expr) = ADT(ADTType(Utils.webStyle, Seq()), Seq(key, value))
  def _Some[A: Constrainable](e: Expr) = ADT(ADTType(Utils.some, Seq(inoxTypeOf[A])), Seq(e))
  def _None[A: Constrainable] = ADT(ADTType(Utils.none, Seq(inoxTypeOf[A])), Seq())
  def _Left[A: Constrainable, B: Constrainable](e: Expr) = ADT(ADTType(Utils.left, Seq(inoxTypeOf[A], inoxTypeOf[B])), Seq(e))
  def _Right[A: Constrainable, B: Constrainable](e: Expr) = ADT(ADTType(Utils.right, Seq(inoxTypeOf[A], inoxTypeOf[B])), Seq(e))
  def _XMLAttribute(key: Expr, value: Expr) = ADT(ADTType(Utils.xmlAttribute, Seq()), Seq(key, value))
  def _XMLNode(tag: Expr, attributes: Expr, children: Expr) =
    ADT(ADTType(Utils.xmlNode, Seq()), Seq(tag, attributes, children))
}
import Constrainable._

abstract class Tree[LeafValue, NodeValue]

case class Node[LeafValue, NodeValue](left: Tree[LeafValue, NodeValue], value: NodeValue, right: Tree[LeafValue, NodeValue]) extends Tree[LeafValue, NodeValue]
case class Leaf[LeafValue, NodeValue](value: LeafValue) extends Tree[LeafValue, NodeValue]

abstract class GeneralConstraint[A <: GeneralConstraint[A]](protected val formula: Expr,
                                 functions: Map[Identifier, ManualReverse[_, _]])
{
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

  def copyWithNewFormula(newFormula: Expr): A

  /** Simplify the formula by replacing String method calls, removing equalities between identifiers */
  def simplify(solutionVars: Set[Variable]): A = {
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
        val topEqualities = ands.collect{
          case Equals(v1: Variable, v2: Variable) => (if(!solutionVars(v1)) v1 -> v2 else v2 -> v1):(Expr, Expr)
        }
        val tewi = topEqualities.zipWithIndex
        val topEqualitiesMap = tewi.filter{
          case ((i1, i2), i) => if(tewi.exists{
            case ((j1, j2), j) => j < i && j1 == i2
          }) {
            false // We remove back arrow assignments so that the assignment map is only forward.
          } else true
        }.map(_._1).toMap
        // Prevent loops.
        def transitiveTopEqualities(x: Expr): Option[Expr] = topEqualitiesMap.get(x) match {
          case Some(newVar) => transitiveTopEqualities(newVar).orElse(Some(newVar))
          case None => None
        }
        inox.trees.exprOps.postMap(transitiveTopEqualities _)(x)
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

    copyWithNewFormula(finalFormula)
  }

  /** Converts the formula to a stream of conjuncts, each of one being able to yield solutions*/
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

  /** Separates the "Maybe(a == b)" statements from the conjunct*/
  def splitMaybe(e: Seq[Expr], notMaybes: Seq[Expr], maybes: Seq[Equals]): (List[Expr], List[Equals]) = {
    e match {
      case Seq() => (notMaybes.reverse.toList, maybes.reverse.toList)
      case FunctionInvocation(Common.maybe, _, Seq(equality@Equals(a, b))) +: tail =>
        splitMaybe(tail, notMaybes, equality +: maybes)
      case a +: tail =>
        splitMaybe(tail, a +: notMaybes, maybes)
    }
  }

  /** An "Equals" here is the inner content of a "Maybe". We want to satisfy most of them if possible.
    * If a combination of maybe is satisfiables with e._1, no sub-combination should be tested.
    * The Int is startToDeleteAt: Int = 0, a way to know the number of Equals from the beginning we should not remove.
    **/
  def maxSMTMaybes(es: Stream[(List[Expr], List[Equals], Int)]): Stream[(ThisSolver, prog.Model)] = {
    if(es.isEmpty) return Stream.empty
    val e = es.head

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
    val constPart = e._1
    val maybePart = e._2
    val numForceMaybeToKeep = e._3
    //println("The maybes are: " + e._2)

    val solver = prog.getSolver.getNewSolver
    //println("solving " + and(e._1 ++ e._2 : _*))
    solver.assertCnstr(and(e._1 ++ e._2 : _*))
    //println("#2")
    solver.check(SolverResponses.Model) match {
      case SatWithModel(model) =>
        //println("One solution !")
        val updatedStream = es.filterNot{ _._2.toSet.subsetOf(maybePart.toSet)}

        (solver, model) #:: maxSMTMaybes(updatedStream)
      case _ =>
        //println("No solution. Removing maybes...")
        maxSMTMaybes(es.tail #::: {
          for {i <- (numForceMaybeToKeep until e._2.length).toStream
               seq = e._2.take(i) ++ e._2.drop(i + 1)
          } yield (constPart, seq, numForceMaybeToKeep)
        })
    }
  }

  /** Given a formula splitted at manual reversing functions (the tree t), returns a stream of solvers and associated modles.*/
  def solveTrees(t: Tree[Seq[Expr], Expr]): Stream[(ThisSolver, prog.Model)] = {
    t match {
      case Leaf(seqExpr) =>
        val (eqs, maybes)  = splitMaybe(seqExpr, Nil, Nil)
        for{ solver <- maxSMTMaybes(Stream((eqs, maybes, 0))) } yield solver
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
              (eqs, maybes)  = splitMaybe(newSeqExpr, Nil, Nil)
              //_ = println("Solving maybe:" + x)
              solver <- maxSMTMaybes(Stream((eqs, maybes, 0)))
        } yield {
          solver
        }

      case _ => throw new Exception("[Internal error] Does not support this shape of tree : " + t)
    }
  }

  /** Given an input variable, returns a stream of models with valuations of this variable */
  def getStreamOfSolutions(inputVar: Variable, e: (ThisSolver, prog.Model)): Stream[prog.Model] = {
    val solver = e._1
    val solutionInit = e._2
    //println(s"Looking for $inputVar in $solutionInit")
    val solutionInitExpr: Expr = solutionInit.vars(inputVar.toVal  : inox.trees.ValDef)
    //println("Found solution " + solutionInitExpr)
    //println("Supposing " + !(inputVar === solutionInit))

    def otherSolutions(prevSol: inox.trees.Expr): Stream[prog.Model] = {
      solver.check(SolverResponses.Model) match {
        case SatWithModel(model) =>
          // We are going to plug in the maximum number of equals possible until it breaks.
          val solution: Expr = model.vars(inputVar.toVal  : inox.trees.ValDef)
          //println("Found solution " + solution)
          if (prevSol == solution) Stream.empty else {
            model #:: {
              //println("Supposing " + !(inputVar === solution))
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

  /** Returns a stream of solutions satisfying the constraint */
  def toStreamOfInoxExpr(solutionVar: inox.trees.Variable): Stream[Expr] = {
    val simplified = simplify(Set(solutionVar)).formula

    println("######## Converting this formula to stream of solutions ######\n" + simplified)


    // The stream of conjuncts splitted with the maybes.
    for {a <- getStreamOfConjuncts(simplified)
         _ = println("Solving conjunct : " + a)
         splitted = splitAtUnknownFunctions(a)
         solver <- solveTrees(splitted)
         modelInox <- getStreamOfSolutions(solutionVar, solver)
         solutionInox = modelInox.vars(solutionVar.toVal: inox.trees.ValDef)
    }
      yield {
        solutionInox
      }
  }
}

/** A wrapper around an inox Expr which can enumerate solutions*/
case class Constraint[A: Constrainable](protected val _formula: Expr,
                                        functions: Map[Identifier, ManualReverse[_, _]] = Map())
  extends GeneralConstraint[Constraint[A]](_formula, functions) {
  /** Adds a new assignment to this constraint */
  def apply[A: Constrainable](tuple: (inox.trees.Variable, A)) = this && tuple._1 === inoxExprOf[A](tuple._2)

  /** Adds a new conjunct to this constraint */
  def &&(b: Expr) = Constraint[A](formula && b, functions)

  /** Adds a new conjunct to this constraint */
  def &&[B: Constrainable](b: Constraint[B]): Constraint[A] = Constraint[A](formula && b.formula, functions ++ b.functions)
  def <&&[B: Constrainable](b: Constraint[B]): Constraint[B] = Constraint[B](formula && b.formula, functions ++ b.functions)

  import inox.solvers._
  import SolverResponses._

  def copyWithNewFormula(newFormula: Expr): Constraint[A] = {
    Constraint[A](newFormula, functions)
  }

  /** Returns a stream of solutions satisfying the constraint */
  def toStream(solutionVar: inox.trees.Variable): Stream[A] = {
    toStreamOfInoxExpr(solutionVar).map(exprOfInox[A] _)
  }
}

case class InoxConstraint(protected val _formula: Expr, functions: Map[Identifier, ManualReverse[_, _]] = Map())
extends GeneralConstraint[InoxConstraint](_formula, functions)
{
  def copyWithNewFormula(newFormula: Expr) = this.copy(_formula = newFormula)

}