package perfect
import org.scalatest._
import matchers._
import Matchers.{=== => _, _}
import ReverseProgram.FunctionEntry
import Utils._
import WebTrees._
import inox._
import inox.evaluators.EvaluationResults
import inox.trees.{not => inoxNot, _}
import inox.trees.dsl._
import perfect.ProgramFormula.{ListInsert, TreeModification}

/**
  * Created by Mikael on 28/04/2017.
  */
class WebTest extends FunSuite with TestHelpers {
  import InoxConvertible._
  import ImplicitTuples._
  import XmlTrees._
  implicit val symbols = Utils.defaultSymbols

  object Bold {
    val TWebElement = inoxTypeOf[WebElement]
    def apply(e: Expr): Expr = {
      _Element("b", _List[WebElement](_WebElement(e)))
    }
    def unapply(e: Expr): Option[Expr] = e match {
      case _Element(StringLiteral("b"),_List(TWebElement, _WebElement(e)), _, _) => Some(e)
      case _ => None
    }
  }


  test("Split a string to insert bold") {
    Log activated {
      val pfun = _Element("div", _List[WebElement](
        _WebElement(_TextNode("This is some text"))
      ))
      val repaired = TreeModification(
        inoxTypeOf[Element],
        inoxTypeOf[List[WebElement]],
        pfun,
        ListInsert.Expr(
          inoxTypeOf[WebElement],
          Nil,
          List(_WebElement(_TextNode("This is ")), _WebElement(Bold(_TextNode("some"))), _WebElement(_TextNode(" text"))),
          Nil
        ),
        List(Utils.children)
      )
      pfun repairFrom repaired shouldEqual
        _Element("div", _List[WebElement](
          _WebElement(_TextNode("This is ")),
          _WebElement(Bold(_TextNode("some"))),
          _WebElement(_TextNode(" text"))
        ))
    }
  }

  test("Split a variable to insert bold") {

  }
}
