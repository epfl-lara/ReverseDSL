package perfect
import legacy._
import perfect.ProgramFormula.TreeModification
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

  val pfWithoutSortingFlatmap = {
    /** Select the first child with the given name */
    val selectChildImpl = \("in"::TNode, "i2"::String)((i1Node, i2String) =>
      FunctionInvocation(filter, Seq(tNode), Seq(i1Node.getField(children),
        \("i3"::TNode)(i3Node => i3Node.getField(tag) === i2String)
      ))
    )

    let("selectChild"::inoxTypeOf[(Node, String) => List[Node]], selectChildImpl)(selectChildv =>
      let("in"::TNode, inoxExprOf[Node](input))(inVariable =>
        _Node("addrbook", children=
          FunctionInvocation(listconcat, Seq(tNode),
            Seq(
              _List[Node](_Node("index", children=
                FunctionInvocation(flatmap, Seq(tNode, tNode), Seq(inVariable.getField(children),
                  \("n"::TNode)(nInput => Application(selectChildv, Seq(nInput, "name")))
                )))),
              inVariable.getField(children)
            )
          )
        )))
  }

  val pfWithoutSorting = {
    val selectChild = valdef[(Node, String) => List[Node]]("selectChild")
    /** Select the first child with the given name */
    val selectChildImpl = \("i1"::TNode, "i2"::String)((i1Node, i2String) =>
      FunctionInvocation(filter, Seq(tNode), Seq(i1Node.getField(children),
        \("i3"::TNode)(i3Node => i3Node.getField(tag) === i2String)
      ))
    )

    val getOrElse = valdef[(Node, String, String) => String]("getOrElse")
    val getOrElseImpl = \("n"::TNode, "k"::String, "d"::String)((fInput, kInput, dInput) =>
      let("k"::T(list)(tNode), Application(selectChild.toVariable, Seq(fInput, kInput)))(k =>
        if_(k.isInstOf(T(cons)(tNode))) {
          let("l"::T(list)(tNode), k.asInstOf(T(cons)(tNode)).getField(head).getField(children))(l =>
            if_(l.isInstOf(T(cons)(tNode))) {
              l.asInstOf(T(cons)(tNode)).getField(head).getField(tag)
            } else_ dInput
          )
        } else_ dInput
      )
    )
    val obtainNameImpl = \("n"::TNode)(nInput =>
      _Node("name", children=_List[Node](_Node(Application(getOrElse.toVariable, Seq(nInput, "name", "")))))
    )

    let("in"::TNode, inoxExprOf[Node](input))(inVariable =>
      let(selectChild, selectChildImpl)(selectChildv =>
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
  }

  val pfWithSorting = {
    val selectChild = valdef[(Node, String) => List[Node]]("selectChild")
    /** Select the first child with the given name */
    val selectChildImpl = \("i1"::TNode, "i2"::String)((i1Node, i2String) =>
      FunctionInvocation(filter, Seq(tNode), Seq(i1Node.getField(children),
        \("i3"::TNode)(i3Node => i3Node.getField(tag) === i2String)
      ))
    )

    val getOrElse = valdef[(Node, String, String) => String]("getOrElse")
    val getOrElseImpl = \("n"::TNode, "k"::String, "d"::String)((fInput, kInput, dInput) =>
      let("k"::T(list)(tNode), Application(selectChild.toVariable, Seq(fInput, kInput)))(k =>
        if_(k.isInstOf(T(cons)(tNode))) {
          let("l"::T(list)(tNode), k.asInstOf(T(cons)(tNode)).getField(head).getField(children))(l =>
            if_(l.isInstOf(T(cons)(tNode))) {
              l.asInstOf(T(cons)(tNode)).getField(head).getField(tag)
            } else_ dInput
          )
        } else_ dInput
      )
    )
    val obtainNameImpl = \("n"::TNode)( nInput =>
      _Node("name", children=_List[Node](_Node(Application(getOrElse.toVariable, Seq(nInput, "name", "")))))
    )

    let("in"::TNode, inoxExprOf[Node](input))(inVariable =>
      let(selectChild, selectChildImpl)(selectChildv =>
        let(getOrElse, getOrElseImpl)(getOrElsev =>
          let("childrenSortedByName"::inoxTypeOf[List[Node]],
            FunctionInvocation(sortWith, Seq(inoxTypeOf[Node]), Seq(
              inVariable.getField(children),
              \("n1"::TNode, "n2"::TNode)((n1, n2) =>
                -FunctionInvocation(stringCompare, Seq(), Seq(
                  Application(getOrElsev, Seq(n1, StringLiteral("name"), StringLiteral(""))),
                  Application(getOrElsev, Seq(n2, StringLiteral("name"), StringLiteral(""))))))
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
  }

  test("Node") {
    val input: Node = <test>This is a test</test>
    val newOut: Expr = "tist"
    val expectedOut: Node = <tist>This is a test</tist>
    val pf = ADTSelector(input, tag)
    implicit val s = Utils.defaultSymbols

    pf repairFrom newOut shouldProduce newOut match {
      case ADTSelector(ADT(_, Seq(StringLiteral(s), _, _)), _) =>
        s shouldEqual "tist"
    }
  }

  val initialOutWithoutSorting: Node = <addrbook>
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

  test("Hu 2004 without sorting") {
    pfWithoutSorting shouldProduce initialOutWithoutSorting
  }
  test("Hu 2004 without sorting modification in name") {
    /*val newOutModification: Node = <addrbook>
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
    </addrbook>*/
    import Utils._
    val newOutModification: ProgramFormula = ProgramFormula.TreeModification(
      inoxTypeOf[Node],
      inoxTypeOf[String],
      initialOutWithoutSorting,
      "Prof. Masato Takeichi",
      List(children, head, children, head, children, head, tag)
    )(Utils.defaultSymbols)

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
    /*val newOutInsertionData: Node = <addrbook>
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
    </addrbook>*/
    implicit val symbols = Utils.defaultSymbols
    val newOutInsertionData: ProgramFormula =
      ProgramFormula.TreeModification(inoxTypeOf[Node],inoxTypeOf[List[Node]],initialOutWithoutSorting,
        ProgramFormula.ListInsert.Expr(inoxTypeOf[Node],
          List(<index>
            <name>Masato Takeichi</name>
            <name>Zhenjiang Hu</name>
            <name>Shin-Cheng Mu</name>
          </index>: Node,
            <person>
              <name>Masato Takeichi</name>
              <email>takeichi@acm.org</email>
              <tel>+81-3-5841-7430</tel>
            </person>: Node,
            <person>
              <name>Zhenjiang Hu</name>
              <email>hu@mist.i.u-tokyo.ac.jp</email>
              <email>hu@ipl.t.u-tokyo.ac.jp</email>
              <tel>+81-3-5841-7411</tel>
            </person>: Node),
          List(
            <person>
              <name>Mikael Mayer</name>
              <email>mikael@mayer.tk</email>
              <tel>+41-787-330-1924</tel>
            </person>: Node
          ),
          List(
            <person>
              <name>Shin-Cheng Mu</name>
              <email>scm@mist.i.u-tokyo.ac.jp</email>
              <tel>+81-3-5841-7411</tel>
            </person>: Node
          )
        ), List(Utils.children)
      )

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
    import Utils._
    val newOutInsertionIndex = TreeModification(
      inoxTypeOf[Node],
      inoxTypeOf[List[Node]],
      initialOutWithoutSorting,
      ProgramFormula.ListInsert.Expr(inoxTypeOf[Node],
        List(
          <name> Masato Takeichi </name>: Node,
            <name> Zhenjiang Hu </name>: Node),
        List(<name> Mikael Mayer </name>: Node),
        List(<name> Shin-Cheng Mu </name>: Node)
      )
      , List(children, head, children)
    )(Utils.defaultSymbols)/*
    val newOutInsertionIndex: Node =
      <addrbook>
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
    </addrbook>*/

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
        <name> Mikael Mayer </name>
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
