package perfect

/**
  * Created by Mikael on 23/03/2017.
  */

object WebTrees {
  private var displayNiceDSL = true

  implicit def toWebTree(i: InnerWebElement) = WebElement(i)
  implicit def toWebTree2(i: List[InnerWebElement]): List[WebTree] = i.map(WebElement.apply _)

  abstract class WebTree extends Product with Serializable
  case class WebElement(inner: InnerWebElement) extends WebTree
  abstract class InnerWebElement
  case class TextNode(text: String) extends InnerWebElement {
    override def toString = if(displayNiceDSL) "\"" + "\"".r.replaceAllIn("\\\\".r.replaceAllIn(text, "\\\\\\\\"), "\\\"") + "\"" else s"TextNode($text)"
  }
  object TextNode
  object Element
  import InoxConvertible._

  case class Element(tag: String, children: List[WebElement] = Nil, attributes: List[WebAttribute] = Nil, styles: List[WebStyle] = Nil) extends InnerWebElement {
    override def toString = if(displayNiceDSL) "<." + tag + (if(children.nonEmpty || attributes.nonEmpty || styles.nonEmpty) (children ++ attributes ++ styles).mkString("(", ", ", ")") else "") else {
      if(styles.isEmpty) {
        if(attributes.isEmpty) {
          if(children.isEmpty) {
            s"Element($tag)"
          } else {
            s"Element($tag,$children)"
          }
        } else {
          s"Element($tag,$children,$attributes)"
        }
      } else
        s"Element($tag,$children,$attributes,$styles)"
    }
  }
  case class WebAttribute(name: String, value: String) extends WebTree {
    override def toString = if(displayNiceDSL) "^." + name + " := " + value else super.toString
  }
  case class WebStyle(name: String, value: String) extends WebTree {
    override def toString = if(displayNiceDSL) "^." + name + " := " + value else super.toString
  }
}
import WebTrees._
import legacy.{Const, Implicits, MapReverse, PairSame}
