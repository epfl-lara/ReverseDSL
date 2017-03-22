/**
  * Created by Mikael on 07/03/2017.
  */
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


class XmlTest extends FunSuite with TestHelpers {
  import InoxConvertible._

  test("Hu 2004 conversion") {
    val input: XmlTrees.Node = <addrbook>
      <person>
        <name> Masato Takeichi </name>
        <email> takeichi@acm.org </email>
        <tel> +81-3-5841-7430 </tel>
      </person>
      <person>
        <name> Zhenjiang Hu </name>
        <email> hu@mist.i.u-tokyo.ac.jp </email>
        <email> hu@ipl.t.u-tokyo.ac.jp </email>
        <tel> +81-3-5841-7411 </tel>
      </person>
      <person>
        <name> Shin-Cheng Mu </name>
        <email> scm@mist.i.u-tokyo.ac.jp </email>
        <tel> +81-3-5841-7411 </tel>
      </person>
    </addrbook>

    val expectedOut: XmlTrees.Node = <addrbook>
      <index>
        <name> Zhenjiang Hu </name>
        <name> Shin-Cheng Mu </name>
        <name> Masato Takeichi </name>
      </index>
      <person>
        <name> Zhenjiang Hu </name>
        <email> hu@mist.i.u-tokyo.ac.jp </email>
        <email> hu@ipl.t.u-tokyo.ac.jp </email>
        <tel> +81-3-5841-7411 </tel>
      </person>
      <person>
        <name> Shin-Cheng Mu </name>
        <email> scm@mist.i.u-tokyo.ac.jp </email>
        <tel> +81-3-5841-7411 </tel>
      </person>
      <person>
        <name> Masato Takeichi </name>
        <email> takeichi@acm.org </email>
        <tel> +81-3-5841-7430 </tel>
      </person>
    </addrbook>

    val in = ValDef(FreshIdentifier("in"), inoxTypeOf[XmlTrees.Node], Set())

    val selectChildInput1 = ValDef(FreshIdentifier("i1"), inoxTypeOf[XmlTrees.Node], Set())
    val selectChildInput2 = ValDef(FreshIdentifier("i2"), inoxTypeOf[String], Set())
    val selectChildSubInput1 = ValDef(FreshIdentifier("i3"), inoxTypeOf[XmlTrees.Node], Set())
    val selectChild = ValDef(FreshIdentifier("selectChild"), FunctionType(Seq(inoxTypeOf[XmlTrees.Node], inoxTypeOf[String]), inoxTypeOf[List[XmlTrees.Node]]))
    val selectChildImpl = Lambda(Seq(selectChildInput1, selectChildInput2),
      Application(Variable(filter, FunctionType(Seq(inoxTypeOf[List[XmlTrees.Node]], inoxTypeOf[String]), inoxTypeOf[List[XmlTrees.Node]]), Set()), Seq(selectChildInput1.toVariable.getField(children),
        Lambda(Seq(selectChildSubInput1), selectChildSubInput1.toVariable.getField(tag) === selectChildInput2.toVariable)
      ))
    )

    val obtainNameInput = ValDef(FreshIdentifier("n"), inoxTypeOf[XmlTrees.Node], Set())
    val obtainName = Variable(FreshIdentifier("obtainName"), FunctionType(Seq(inoxTypeOf[XmlTrees.Node]), inoxTypeOf[String]), Set())
    /*val obtainNameImpl = Lambda(Seq(nameVd),
      nameVd.toVariable.children
    )*/

    /*val funDef = function(
      let(in, inoxExprOf[XmlTrees.Node](input))(inVariable =>
        let(obtainName, Lambda(Seq(nameVar),


        )))
        _XMLNode("addrbook", _List[XmlTrees.XMLAttribute](),
      )
    )(inoxTypeOf[XmlTrees.Node])*/


  }
}
