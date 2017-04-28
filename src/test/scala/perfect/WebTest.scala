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
import perfect.ProgramFormula._

/**
  * Created by Mikael on 28/04/2017.
  */
class WebTest extends FunSuite with TestHelpers {
  import InoxConvertible._
  import ImplicitTuples._
  import XmlTrees._
  import StringConcatExtended._
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
    Log.activated {
      val pfun = _Element("div", _List[WebElement](
        _WebElement(_TextNode("This is some text"))
      ))
      val repaired = PatternMatch.Expr.Build(
        ("t" :: StringType, "This "),
        ("is_some" :: StringType, "is some"),
        ("text" :: StringType, " text")) { case Seq(t, is_some, text) =>
        (_Element("div", _List[WebElement](
          _WebElement(_TextNode(t +& is_some +& text))
        )),
          _Element("div", _List[WebElement](
            _WebElement(_TextNode(t)),
            _WebElement(Bold(_TextNode(is_some))),
            _WebElement(_TextNode(text))
          )))
      }
      pfun repairFrom repaired shouldEqual
        _Element("div", _List[WebElement](
          _WebElement(_TextNode("This ")),
          _WebElement(Bold(_TextNode("is some"))),
          _WebElement(_TextNode(" text"))
        ))
    }
  }

  test("Split a variable to insert bold") {
    val pfun = let("sometext" :: String, "some text")(sometext =>
      _Element("div", _List[WebElement](
        _WebElement(_TextNode("This is " +& sometext))
      )))
    val original = eval(pfun)

    val repaired = PatternMatch.Expr.Build(
      ("t"::StringType, "This "),
      ("is_some"::StringType, "is some"),
      ("text"::StringType, " text")){ case Seq(t, is_some, text) =>
      (_Element("div", _List[WebElement](
        _WebElement(_TextNode(t +& is_some +& text))
      )),
        _Element("div", _List[WebElement](
          _WebElement(_TextNode(t)),
          _WebElement(Bold(_TextNode(is_some))),
          _WebElement(_TextNode(text))
        )))
    }

    val (someV, textV, body) = pfun repairFrom repaired match {
      case Let(someVd, StringLiteral("some"), Let(textVd, StringLiteral(" text"), Let(sometextvd, someV +& textV, body))) =>
        (someVd.toVariable, textVd.toVariable, body)
      case Let(textVd, StringLiteral(" text"), Let(someVd, StringLiteral("some"), Let(sometextvd, someV +& textV, body))) =>
        (someVd.toVariable, textVd.toVariable, body)
    }

    body shouldEqual
      _Element("div", _List[WebElement](
        _WebElement(_TextNode("This ")),
        _WebElement(Bold(_TextNode("is " +& someV))),
        _WebElement(_TextNode(textV))
      ))
  }
}
