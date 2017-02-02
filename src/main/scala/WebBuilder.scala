import scala.language.dynamics
import shapeless.{:: => #:, HList, HNil}

object WebBuilder {
  import WebTrees._
  
  import Implicits._
  
  
  object < extends Dynamic {
    def apply(name: String) = Const[Element](Element(name, Nil, Nil, Nil))
    val span = apply("span")
    val div = apply("div")
    val ul = apply("ul")
    val li = apply("li")
    def selectDynamic(name: String) = apply(name)
  }
}