package legacy

import shapeless.{:: => #:}

import scala.language.dynamics
import perfect.WebTrees._

object WebBuilder {
  
  
  object < extends Dynamic {
    def apply(name: String) = Const[Unit, Element](Element(name, Nil, Nil, Nil))
    val span = apply("span")
    val div = apply("div")
    val ul = apply("ul")
    val li = apply("li")
    def selectDynamic(name: String) = apply(name)
  }
}