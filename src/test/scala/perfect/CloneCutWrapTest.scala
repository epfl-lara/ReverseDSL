package perfect
import inox._
import inox.trees._
import inox.trees.dsl._
import org.scalatest.FunSuite

/**
  * Created by Mikael on 27/03/2017.
  */
class CloneCutWrapTest extends FunSuite with TestHelpers {
  import InoxConvertible._
  import XmlTrees._
  test("Wrap") {
    val output = _Node("i", children=_List[Node](_Node("Hello")))
    val pfun = function(
      let("ad" :: inoxTypeOf[String], "Hello"){ av =>
        _Node("i", children=_List[Node](_Node(av)))
      }
    )(inoxTypeOf[Node])
    checkProg(output, pfun)
    //repairProgram(pfun, )
  }

  test("Unwrap") {

  }

  test("Split") {

  }

  test("Clone") {

  }

  test("Cut") {

  }
}
