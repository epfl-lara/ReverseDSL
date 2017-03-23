package perfect
import ImplicitTuples._
import inox._
import inox.trees._
import inox.trees.dsl._
import inox.solvers._
import inox.InoxProgram

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
  val xmlNode: Identifier = FreshIdentifier("Node")
  val xmlAttribute: Identifier = FreshIdentifier("Attribute")

  val maybe : Identifier = FreshIdentifier("maybe")


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
  val map = FreshIdentifier("map")
  val listconcat = FreshIdentifier("append")
  val flatten = FreshIdentifier("flatten")
  val flatmap = FreshIdentifier("flatMap")

  val defaultSymbols =
    NoSymbols.withADTs(allConstructors)

  @inline def castOrFail[A, B <: A](a: A): B =
    a.asInstanceOf[B]

  @inline def asStr(e: Expr): String = castOrFail[Expr, StringLiteral](e).value
}
