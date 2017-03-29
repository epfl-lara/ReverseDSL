package perfect
import legacy._
import perfect.Utils.children

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
  import ImplicitTuples._
  import XmlTrees._

  val input: Node = <addrbook>
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

  val tListNode = inoxTypeOf[List[Node]]
  val tString = inoxTypeOf[String]
  val tNode = inoxTypeOf[Node]

  val pfWithoutSortingFlatmap: PFun = {
    val in = valdef[Node]("in")
    val i1Node = valdef[Node]("i1")
    val i2String = valdef[String]("i2")
    val i3Node = valdef[Node]("i3")
    val selectChild = valdef[(Node, String) => List[Node]]("selectChild")
    /** Select the first child with the given name */
    val selectChildImpl = Lambda(Seq(i1Node, i2String),
      FunctionInvocation(filter, Seq(tNode), Seq(i1Node.toVariable.getField(children),
        Lambda(Seq(i3Node), i3Node.toVariable.getField(tag) === i2String.toVariable)
      ))
    )

    val nInput = valdef[Node]("n")

    val pf = function(
      let(selectChild, selectChildImpl)(selectChildv =>
        let(in, inoxExprOf[Node](input))(inVariable =>
          _Node("addrbook", children=
            FunctionInvocation(listconcat, Seq(tNode),
              Seq(
                _List[Node](_Node("index", children=
                  FunctionInvocation(flatmap, Seq(tNode, tNode), Seq(inVariable.getField(children), Lambda(Seq(nInput),
                    Application(selectChild.toVariable, Seq(nInput.toVariable, "name"))
                  ))) )),
                inVariable.getField(children)
              )
            )
          )))
    )(tNode)

    pf
  }

  val pfWithoutSorting: PFun = {
    val in = valdef[Node]("in")
    val i1Node = valdef[Node]("i1")
    val i2String = valdef[String]("i2")
    val i3Node = valdef[Node]("i3")
    val selectChild = valdef[(Node, String) => List[Node]]("selectChild")
    /** Select the first child with the given name */
    val selectChildImpl = Lambda(Seq(i1Node, i2String),
      FunctionInvocation(filter, Seq(tNode), Seq(i1Node.toVariable.getField(children),
        Lambda(Seq(i3Node), i3Node.toVariable.getField(tag) === i2String.toVariable)
      ))
    )
    val n1 = valdef[Node]("n1")
    val n2 = valdef[Node]("n2")

    val fInput = valdef[Node]("n")
    val kInput = valdef[String]("k")
    val dInput = valdef[String]("d")
    val getOrElse = valdef[(Node, String, String) => String]("getOrElse")
    val getOrElseImpl = Lambda(Seq(fInput, kInput, dInput),
      let("k"::T(list)(tNode), Application(selectChild.toVariable, Seq(fInput.toVariable, kInput.toVariable)))(k =>
        if_(k.isInstOf(T(cons)(tNode))) {
          let("l"::T(list)(tNode), k.asInstOf(T(cons)(tNode)).getField(head).getField(children))(l =>
            if_(l.isInstOf(T(cons)(tNode))) {
              l.asInstOf(T(cons)(tNode)).getField(head).getField(tag)
            } else_ dInput.toVariable
          )
        } else_ dInput.toVariable
      )
    )
    val nInput = valdef[Node]("n")
    val obtainNameImpl = Lambda(Seq(nInput),
      _Node("name", children=_List[Node](_Node(Application(getOrElse.toVariable, Seq(nInput.toVariable, "name", "")))))
    )

    val pf = function(
      let(in, inoxExprOf[Node](input))(inVariable =>
        let(selectChild, selectChildImpl)(selectChildv =>
          //let(obtainName, obtainNameImpl)(obtainv =>
          let(getOrElse, getOrElseImpl)(getOrElsev =>
              _Node("addrbook", children=
                FunctionInvocation(listconcat, Seq(tNode),
                  Seq(
                    _List[Node](_Node("index", children=
                      FunctionInvocation(map, Seq(tNode, tNode), Seq(inVariable.getField(children), obtainNameImpl)) )),
                    inVariable.getField(children)
                  )
                )
              ))))
    )(tNode)
    pf
  }

  val pfWithSorting = {
    val in = valdef[Node]("in")
    val i1Node = valdef[Node]("i1")
    val i2String = valdef[String]("i2")
    val i3Node = valdef[Node]("i3")
    val selectChild = valdef[(Node, String) => List[Node]]("selectChild")
    /** Select the first child with the given name */
    val selectChildImpl = Lambda(Seq(i1Node, i2String),
      FunctionInvocation(filter, Seq(tNode), Seq(i1Node.toVariable.getField(children),
        Lambda(Seq(i3Node), i3Node.toVariable.getField(tag) === i2String.toVariable)
      ))
    )
    val n1 = valdef[Node]("n1")
    val n2 = valdef[Node]("n2")

    val fInput = valdef[Node]("n")
    val kInput = valdef[String]("k")
    val dInput = valdef[String]("d")
    val getOrElse = valdef[(Node, String, String) => String]("getOrElse")
    val getOrElseImpl = Lambda(Seq(fInput, kInput, dInput),
      let("k"::T(list)(tNode), Application(selectChild.toVariable, Seq(fInput.toVariable, kInput.toVariable)))(k =>
        if_(k.isInstOf(T(cons)(tNode))) {
          let("l"::T(list)(tNode), k.asInstOf(T(cons)(tNode)).getField(head).getField(children))(l =>
            if_(l.isInstOf(T(cons)(tNode))) {
              l.asInstOf(T(cons)(tNode)).getField(head).getField(tag)
            } else_ dInput.toVariable
          )
        } else_ dInput.toVariable
      )
    )
    val nInput = valdef[Node]("n")
    val obtainNameImpl = Lambda(Seq(nInput),
      _Node("name", children=_List[Node](_Node(Application(getOrElse.toVariable, Seq(nInput.toVariable, "name", "")))))
    )

    val pf = function(
      let(in, inoxExprOf[Node](input))(inVariable =>
        let(selectChild, selectChildImpl)(selectChildv =>
          //let(obtainName, obtainNameImpl)(obtainv =>
          let(getOrElse, getOrElseImpl)(getOrElsev =>
            let("childrenSortedByName"::inoxTypeOf[List[Node]],
              FunctionInvocation(sortWith, Seq(inoxTypeOf[Node]), Seq(
                inVariable.getField(children),
                Lambda(Seq(n1, n2),
                  -FunctionInvocation(stringCompare, Seq(), Seq(
                    Application(getOrElsev, Seq(n1.toVariable, StringLiteral("name"), StringLiteral(""))),
                    Application(getOrElsev, Seq(n2.toVariable, StringLiteral("name"), StringLiteral(""))))))
              ))
            )(childrenSortedByName =>
              _Node("addrbook", children=
                FunctionInvocation(listconcat, Seq(tNode),
                  Seq(
                    _List[Node](_Node("index", children=
                      FunctionInvocation(map, Seq(tNode, tNode), Seq(childrenSortedByName, obtainNameImpl)) )),
                    childrenSortedByName
                  )
                )
              )))))
    )(tNode)
    pf
  }

  test("Node") {
    val input: Node = <test>This is a test</test>
    val newOut: Expr = "tist"
    val expectedOut: Node = <tist>This is a test</tist>
    val pf = function(
      ADTSelector(input, tag)
    )(inoxTypeOf[String])
    implicit val s = Utils.defaultSymbols

    pf repairFrom newOut shouldProduce newOut matchBody {
      case ADTSelector(ADT(_, Seq(StringLiteral(s), _, _)), _) =>
        s shouldEqual "tist"
    }
  }

  test("Hu 2004 without sorting") {
    val initialOut: Node = <addrbook>
      <index>
        <name>Masato Takeichi</name>
        <name>Zhenjiang Hu</name>
        <name>Shin-Cheng Mu</name>
      </index>
      <person>
        <name>Masato Takeichi</name>
        <email>takeichi@acm.org</email>
        <tel>+81-3-5841-7430</tel>
      </person>
      <person>
        <name>Zhenjiang Hu</name>
        <email>hu@mist.i.u-tokyo.ac.jp</email>
        <email>hu@ipl.t.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
      <person>
        <name>Shin-Cheng Mu</name>
        <email>scm@mist.i.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
    </addrbook>

    checkProg(initialOut, pfWithoutSorting)
  }
  test("Hu 2004 without sorting modification in name") {
    val newOutModification: Node = <addrbook>
      <index>
        <name>Prof. Masato Takeichi</name>
        <name>Zhenjiang Hu</name>
        <name>Shin-Cheng Mu</name>
      </index>
      <person>
        <name>Masato Takeichi</name>
        <email>takeichi@acm.org</email>
        <tel>+81-3-5841-7430</tel>
      </person>
      <person>
        <name>Zhenjiang Hu</name>
        <email>hu@mist.i.u-tokyo.ac.jp</email>
        <email>hu@ipl.t.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
      <person>
        <name>Shin-Cheng Mu</name>
        <email>scm@mist.i.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
    </addrbook>

    val expectedOutModification: Node = <addrbook>
      <index>
        <name>Prof. Masato Takeichi</name>
        <name>Zhenjiang Hu</name>
        <name>Shin-Cheng Mu</name>
      </index>
      <person>
        <name>Prof. Masato Takeichi</name>
        <email>takeichi@acm.org</email>
        <tel>+81-3-5841-7430</tel>
      </person>
      <person>
        <name>Zhenjiang Hu</name>
        <email>hu@mist.i.u-tokyo.ac.jp</email>
        <email>hu@ipl.t.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
      <person>
        <name>Shin-Cheng Mu</name>
        <email>scm@mist.i.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
    </addrbook>
    pfWithoutSorting repairFrom newOutModification shouldProduce expectedOutModification
  }
  test("Hu 2004 without sorting insertion in data") {
    val newOutInsertionData: Node = <addrbook>
      <index>
        <name>Masato Takeichi</name>
        <name>Zhenjiang Hu</name>
        <name>Shin-Cheng Mu</name>
      </index>
      <person>
        <name>Masato Takeichi</name>
        <email>takeichi@acm.org</email>
        <tel>+81-3-5841-7430</tel>
      </person>
      <person>
        <name>Zhenjiang Hu</name>
        <email>hu@mist.i.u-tokyo.ac.jp</email>
        <email>hu@ipl.t.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
      <person>
        <name>Mikael Mayer</name>
        <email>mikael@mayer.tk</email>
        <tel>+41-787-330-1924</tel>
      </person>
      <person>
        <name>Shin-Cheng Mu</name>
        <email>scm@mist.i.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
    </addrbook>

    val expectedOutInsertionData: Node = <addrbook>
      <index>
        <name>Masato Takeichi</name>
        <name>Zhenjiang Hu</name>
        <name>Mikael Mayer</name>
        <name>Shin-Cheng Mu</name>
      </index>
      <person>
        <name>Masato Takeichi</name>
        <email>takeichi@acm.org</email>
        <tel>+81-3-5841-7430</tel>
      </person>
      <person>
        <name>Zhenjiang Hu</name>
        <email>hu@mist.i.u-tokyo.ac.jp</email>
        <email>hu@ipl.t.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
      <person>
        <name>Mikael Mayer</name>
        <email>mikael@mayer.tk</email>
        <tel>+41-787-330-1924</tel>
      </person>
      <person>
        <name>Shin-Cheng Mu</name>
        <email>scm@mist.i.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
    </addrbook>
    pfWithoutSorting repairFrom newOutInsertionData shouldProduce expectedOutInsertionData
  }
  test("Hu 2004 without sorting insertion in index") {
    val newOutInsertionIndex: Node = <addrbook>
      <index>
        <name> Masato Takeichi </name>
        <name> Zhenjiang Hu </name>
        <name> Mikael Mayer </name>
        <name> Shin-Cheng Mu </name>
      </index>
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

    val expectedOutInsertionIndex: Node = <addrbook>
      <index>
        <name> Masato Takeichi </name>
        <name> Zhenjiang Hu </name>
        <name> Mikael Mayer </name>
        <name> Shin-Cheng Mu </name>
      </index>
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

    pfWithoutSorting repairFrom newOutInsertionIndex shouldProduce expectedOutInsertionIndex
  }

  test("Hu 2004") {
    val initialOut: Node = <addrbook>
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

    checkProg(initialOut, pfWithSorting)
  }
  test("Hu 2004 modification in name") {
    val newOutModification: Node = <addrbook>
      <index>
        <name>Zhenjiang Hu</name>
        <name>Shin-Cheng Mu</name>
        <name>Prof. Masato Takeichi</name>
      </index>
      <person>
        <name>Zhenjiang Hu</name>
        <email>hu@mist.i.u-tokyo.ac.jp</email>
        <email>hu@ipl.t.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
      <person>
        <name>Shin-Cheng Mu</name>
        <email>scm@mist.i.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
      <person>
        <name>Masato Takeichi</name>
        <email>takeichi@acm.org</email>
        <tel>+81-3-5841-7430</tel>
      </person>
    </addrbook>

    val expectedOutModification: Node = <addrbook>
      <index>
        <name>Zhenjiang Hu</name>
        <name>Shin-Cheng Mu</name>
        <name>Prof. Masato Takeichi</name>
      </index>
      <person>
        <name>Zhenjiang Hu</name>
        <email>hu@mist.i.u-tokyo.ac.jp</email>
        <email>hu@ipl.t.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
      <person>
        <name>Shin-Cheng Mu</name>
        <email>scm@mist.i.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
      <person>
        <name>Prof. Masato Takeichi</name>
        <email>takeichi@acm.org</email>
        <tel>+81-3-5841-7430</tel>
      </person>
    </addrbook>
    pfWithSorting repairFrom newOutModification shouldProduce expectedOutModification
  }
  test("Hu 2004 insertion in data") {
    val newOutInsertionData: Node = <addrbook>
      <index>
        <name>Zhenjiang Hu</name>
        <name>Shin-Cheng Mu</name>
        <name>Masato Takeichi</name>
      </index>
      <person>
        <name>Zhenjiang Hu</name>
        <email>hu@mist.i.u-tokyo.ac.jp</email>
        <email>hu@ipl.t.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
      <person>
        <name>Mikael Mayer</name>
        <email>mikael@mayer.tk</email>
        <tel>+41-787-330-1924</tel>
      </person>
      <person>
        <name>Shin-Cheng Mu</name>
        <email>scm@mist.i.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
      <person>
        <name>Masato Takeichi</name>
        <email>takeichi@acm.org</email>
        <tel>+81-3-5841-7430</tel>
      </person>
    </addrbook>

    val expectedOutInsertionData: Node = <addrbook>
      <index>
        <name>Zhenjiang Hu</name>
        <name>Shin-Cheng Mu</name>
        <name>Mikael Mayer</name>
        <name>Masato Takeichi</name>
      </index>
      <person>
        <name>Zhenjiang Hu</name>
        <email>hu@mist.i.u-tokyo.ac.jp</email>
        <email>hu@ipl.t.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
      <person>
        <name>Shin-Cheng Mu</name>
        <email>scm@mist.i.u-tokyo.ac.jp</email>
        <tel>+81-3-5841-7411</tel>
      </person>
      <person>
        <name>Mikael Mayer</name>
        <email>mikael@mayer.tk</email>
        <tel>+41-787-330-1924</tel>
      </person>
      <person>
        <name>Masato Takeichi</name>
        <email>takeichi@acm.org</email>
        <tel>+81-3-5841-7430</tel>
      </person>
    </addrbook>
    pfWithSorting repairFrom newOutInsertionData shouldProduce expectedOutInsertionData
  }
  test("Hu 2004 insertion in index") {
    val newOutInsertionIndex: Node = <addrbook>
      <index>
        <name> Zhenjiang Hu </name>
        <name> Mikael Mayer </name>
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

    val expectedOutInsertionIndex: Node = <addrbook>
      <index>
        <name> Zhenjiang Hu </name>
        <name> Shin-Cheng Mu </name>
        <name> Mikael Mayer </name>
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
        <name> Mikael Mayer </name>
      </person>
      <person>
        <name> Masato Takeichi </name>
        <email> takeichi@acm.org </email>
        <tel> +81-3-5841-7430 </tel>
      </person>
    </addrbook>

    pfWithSorting repairFrom newOutInsertionIndex shouldProduce expectedOutInsertionIndex
  }
}
