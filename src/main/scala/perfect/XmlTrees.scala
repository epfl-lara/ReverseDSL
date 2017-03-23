package perfect

import org.apache.commons.lang3.StringEscapeUtils

/**
  * Created by Mikael on 23/03/2017.
  */
object XmlTrees {
  private var displayNiceDSL = true

  case class Node(tag: String, attributes: List[XMLAttribute], children: List[Node]) {
    override def toString = if(displayNiceDSL) {
      "<"+tag+attributes.map(_.toString).mkString+">"+children.map(x => "\n" + x.toString).mkString+"\n</"+tag+">"
    } else s"Node($tag, $attributes, $children)"
  }
  case class XMLAttribute(name: String, value: String) {
    override def toString = if(displayNiceDSL) {
      " " + name + "=\"" + StringEscapeUtils.escapeJava(value) + "\""
    } else s"XMLAttribute($name, $value)"
  }
}
