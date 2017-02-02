import org.scalatest._
import shapeless.syntax.zipper._
import Matchers._

class StringAppendTest extends FunSuite {
  import StringAppend.{put => appendRev, _}
  def doubleAppend(in: (String, String)): String = {
    in._1 + in._2
  }
  import Implicits._
  def doubleAppend2(in: Id[(String, String)]): ((String, String) ~~> String) = {
    in._1 + in._2
  }
  
  test("Double decomposition") {
    doubleAppend(("Hello ", "world")) shouldEqual "Hello world"
    val d = doubleAppend2(Id())
    d.get(("Hello ", "world")) shouldEqual "Hello world"
    d.put("Hello world", ("Hello ", "world")).toList shouldEqual (List(("Hello ", "world")))
    d.put("Hello Buddy", ("Hello ", "world")).toList shouldEqual (List(("Hello ", "Buddy")))
    d.put("Hello  world", ("Hello ", "world")).toList shouldEqual (List(("Hello  ", "world"), ("Hello ", " world")))
    d.put("Hello aworld", ("Hello ", "world")).toList shouldEqual (List(("Hello ", "aworld"), ("Hello a", "world")))
  }
  
  def tripleAppend2(in: Id[((String, String), String)]): (((String, String), String) ~~> String) = {
    in._1._1 + in._1._2 + in._2
  }
  
  test("Triple decomposition") {
    val t = tripleAppend2(Id())

    def tRev(i: String) = t.put(i, Option((("Hello", " "), "world"))).toList.map(ab_c => (ab_c._1._1, ab_c._1._2, ab_c._2))
    tRev("Hello world") shouldEqual List(("Hello", " ", "world"))
    tRev("Hello Buddy") shouldEqual List(("Hello", " ", "Buddy"))
    tRev("Hello big world") shouldEqual List(("Hello"," ","big world"), ("Hello"," big ","world"), ("Hello big"," ","world"))
    tRev("Hello a-world") shouldEqual List(("Hello"," ","a-world"), ("Hello"," a-","world"))
    tRev("Hello-a world") shouldEqual List(("Hello-a"," ","world"), ("Hello","-a ","world"))
    tRev("Hello  world") shouldEqual List(("Hello","  ","world"), ("Hello "," ","world"), ("Hello"," "," world"))
    tRev("Hi world") shouldEqual List(("Hi"," ","world"))
    tRev("Hi Buddy") shouldEqual List()
  }
  
  test("Use of a variable twice") {
    def doubleAppend2(in: Id[(String, String)]): ((String, String) ~~> String) = {
      in._1 + in._2 + in._1
    }
    val d = doubleAppend2(Id())
    d.get(("Hello", " ")) shouldEqual "Hello Hello"
    d.put("Hello Hello", Some(("Hello", " "))).toList shouldEqual List(("Hello", " "))
    d.put("Hello World", Some(("Hello", " "))).toList shouldEqual List(("World", " "))
    d.put("World Hello", Some(("Hello", " "))).toList shouldEqual List(("World", " "))
    d.put("Big World", Some(("Hello", " "))).toList shouldEqual List()
    d.put("Hello  Hello", Some(("Hello", " "))).toList shouldEqual List(("Hello", "  "), ("Hello ", " "), (" Hello", " "))
    d.put("  Hello ", Some((" ", "Hello"))).toList shouldEqual List(("  ", "Hello"), (" ", " Hello"))
    d.put(" Hello  ", Some((" ", "Hello"))).toList shouldEqual List(("  ", "Hello"), (" ", "Hello "))
  }
  
  // Old tests
  /*def f = append(append("Hello", " "), "world")
  def fRev(out: String): List[(String, String, String)] = appendRev(out, ("Hello ", "world")).toList.flatMap(leftRight => 
    appendRev(leftRight._1, ("Hello", " ")).map(lr => (lr._1, lr._2, leftRight._2))
  )
  test("Hello world decomposition") {
    fRev("Hello world") shouldEqual List(("Hello", " ", "world"))
    fRev("Hello Buddy") shouldEqual List(("Hello", " ", "Buddy"))
    fRev("Hello big world") shouldEqual List(("Hello"," ","big world"), ("Hello"," big ","world"), ("Hello big"," ","world"))
    fRev("Hello a-world") shouldEqual List(("Hello"," ","a-world"), ("Hello"," a-","world"))
    fRev("Hello-a world") shouldEqual List(("Hello-a"," ","world"), ("Hello","-a ","world"))
    fRev("Hello  world") shouldEqual List(("Hello","  ","world"), ("Hello "," ","world"), ("Hello"," "," world"))
    fRev("Hi world") shouldEqual List(("Hi"," ","world"))
    fRev("Hi Buddy") shouldEqual List()
  }*/
}

class StringFormatReverseTest extends FunSuite  {
  //import StringFormatReverse._
  import Implicits._
  def format(in: Id[(String, List[Any])]): ((String, List[Any]) ~~> String) = {
    in._1.format(in._2)
  }
  
  test("Formatting reverse decomposition") {
    val f = format(Id())
    def formatRev(s: String, args: List[Any], output: String) =
      f.put(output, Some((s, args)))
    formatRev("%s %s %d", List("Hello", "world", 42), "Hello buddy 42") shouldEqual List(("%s %s %d", List("Hello", "buddy", 42)))
    formatRev("%s,%s %s!", List("Hello", "obscure", "world"), "Hello, obscure world!") should contain (("%s, %s %s!", List("Hello", "obscure", "world")))
    formatRev("%s,%s %s!", List("Hello", "obscure", "world"), "Hello,clear world!") should contain (("%s,%s %s!", List("Hello", "clear", "world")))
    formatRev("%s,%s %s!", List("Hello", "obscure", "world"), "Good bye,awesome friend!") should contain (("%s,%s %s!", List("Good bye", "awesome", "friend")))
    formatRev("%2$s,%3$s %1$s!", List("world", "Hello", "obscure"), "Hello,clear world!") should contain (("%2$s,%3$s %1$s!", List("world", "Hello", "clear")))
    formatRev("Hello %1$s! %1$s is ok?", List("Marion"), "Hello Mikael! Marion is ok?") should contain(("Hello %1$s! %1$s is ok?", List("Mikael")))
    formatRev("Hello %1$s! %1$s is ok?", List("Marion"), "Hello Mikael! Marion is ok?") should not contain (("Hello %1$s! %1$s is ok?", List("Marion")))
  }
  /*
  test("Formatting reverse decomposition") {
    formatRev("%s %s %d", List("Hello", "world", 42), "Hello buddy 42") shouldEqual List(("%s %s %d", List("Hello", "buddy", 42)))
    formatRev("%s,%s %s!", List("Hello", "obscure", "world"), "Hello, obscure world!") should contain (("%s, %s %s!", List("Hello", "obscure", "world")))
    formatRev("%s,%s %s!", List("Hello", "obscure", "world"), "Hello,clear world!") should contain (("%s,%s %s!", List("Hello", "clear", "world")))
    formatRev("%s,%s %s!", List("Hello", "obscure", "world"), "Good bye,awesome friend!") should contain (("%s,%s %s!", List("Good bye", "awesome", "friend")))
    formatRev("%2$s,%3$s %1$s!", List("world", "Hello", "obscure"), "Hello,clear world!") should contain (("%2$s,%3$s %1$s!", List("world", "Hello", "clear")))
    formatRev("Hello %1$s! %1$s is ok?", List("Marion"), "Hello Mikael! Marion is ok?") should contain(("Hello %1$s! %1$s is ok?", List("Mikael")))
    formatRev("Hello %1$s! %1$s is ok?", List("Marion"), "Hello Mikael! Marion is ok?") should not contain (("Hello %1$s! %1$s is ok?", List("Marion")))
  }*/
}


class IntReverseTest extends FunSuite  {
  import IntReverse._

  def fRev(s: Int) = addRev(5, 1, s).flatMap(lr =>
    addRev(2, 3, lr._1).map(lr2 => (lr2._1, lr2._2, lr._2))
  )
  test("(2+3)+1 = 6, 5, 4, 7 repair") {
    fRev(6) shouldEqual List((2,3,1))
    fRev(5) shouldEqual List((2,3,0), (2,2,1), (1,3,1))
    fRev(4) shouldEqual List((2,3,-1), (2,1,1), (0,3,1))
    fRev(7) shouldEqual List((2,3,2), (2,4,1), (3,3,1))
  }
}

class IntValReverseTest extends FunSuite  {
  import IntValReverse._
  
  val source = """
object Prog {
  def main() = {
    val a = 1
    add(add(a, 3), a)
  }
/*
  3 [ a -> 1 ] = add(add(a, 3), a)
  
(add(a, 3), a) in addRev(add(a, 3), a, 3)
(add(a, 3), a) in (2, 1) or (4, -1)
add(a, 3) = 2 <=> (a, 3) in (1, 1) or (-1, 3)
add(a, 3) = 4 <=> (a, 3) in (1, 3)

(a, 3, a) in (1, 1, 1) or (-1, 3, 1) or (1, 3, -1)
Only one possibility, change 3 to 1. Not enough. We miss (0, 3, 0) which changes two values at call site but only one in the final. How to get it? Maybe in this case it's simply not invertible. We cannot afford all possible decompositions if bottom up. Unless abstract representation of all the solutions, such as
def addRev(s: Int, t: Int, out: Int) = (i: Int) =>  {
    (i, out-i)
  } ensuring { ress => ress.forall(res => add(res._1, res._2) == out) }

In this case, we would have:
(add(a, '3), a) in addRev(add(a, 3), a, 3)
So exists i such that
add(a, '3) = i
a = 3-i
Hence
(a, '3) in addRev(a, 3, i)
So there exists j such that
a = j
'3 = i-j
Solve equations => 
3-i = j
Hence
'3 = 2i-3
a = 3-i
Now we test a=1 gives one solution.
We test '3 = 3 gives miraculously one solution
*/
  val expected0 = 5
  val expected1 = 4
  val expected2 = 3
  val expected3 = 6
  val expected4 = 7
}
"""
  def fRev(res: Int): List[(Int, Int)] = {
    //res = add(add(a, 3), a)
    //val i = findInt
    //val lr = addRev(add(a, 3), a, res) (i)
    //(add(a, 3), a) == lr
    //val j = findInt
    //val lr2 = addRev(a, 3, lr._1)
    //assume(a == lr._2 && a == lr2._1 && ifPossible(lr2._2 == 3))
    //yield (a, lr2._2)
    ???
  }

  def test() = {
    //"val a = 1; add(add(a, 3), a)"
    // addRev(a, 3)
    // Would require Z3.
    /*fRev(5) should have 'size 1 //'
    fRev(4) should have 'size 1 //'
    fRev(3) should have 'size 2 //'
    fRev(6) should have 'size 1 //'
    fRev(7) should have 'size 2 //'*/
  }
}

class ListSplitTest extends FunSuite  {
  val f = (x: Int) => x % 2 == 0
  val b = new ListSplit[Int](f)
  import b._
  test("Testing split reverse") {
    splitRev(List(3, 5), (List(3, 5), List(4))) shouldEqual List(List(4, 3, 5), List(3, 4, 5), List(3, 5, 4))
    splitRev(List(3, 4, 5), (List(3, 5), List())) shouldEqual List(List(3, 5))
    splitRev(List(1, 2, 3, 4, 5), (List(1, 3, 5), List(2, 6, 4))) shouldEqual List(List(1, 2, 6, 3, 4, 5), List(1, 2, 3, 6, 4, 5))
  }
}
import WebTrees._

class TypeSplitTest extends FunSuite  {
  import TypeSplit._
  
  test("Recovering split based on type") {
    val initTest = List(WebStyle("width", "100px"), Element("pre"), WebStyle("height", "100px"), WebAttribute("src", "http"))
    
    val sinit = split(initTest)

    splitRev(initTest, (sinit._1, sinit._2, sinit._3(0) :: WebStyle("outline", "bold") :: sinit._3(1) :: Nil)) shouldEqual
    List(List(WebStyle("width","100px"), Element("pre"), WebStyle("outline","bold"), WebStyle("height","100px"), WebAttribute("src","http")))
    splitRev(initTest, (sinit._1, sinit._2, sinit._3(0) :: Nil)) shouldEqual
    List(List(WebStyle("width","100px"), Element("pre"), WebAttribute("src","http")))
  }
}

class WebElementAdditionTest extends FunSuite  {
  import TypeSplit._
  import WebElementAddition._
  val initArg1 = Element("div", Nil, Nil, List(WebStyle("display", "none")))
  val initArg2 = (List(Element("pre")), List(WebAttribute("src", "http")), List(WebStyle("width", "100px"), WebStyle("height", "100px")))
  val sinit = WebElementAddition(initArg1, initArg2._1, initArg2._2, initArg2._3)
  
  // No modification
  val reverseInit = WebElementAddition.applyRev((Element("div", Nil, Nil, List(WebStyle("display", "none"))), (List(Element("pre")), List(WebAttribute("src", "http")), List(WebStyle("width", "100px"), WebStyle("height", "100px")))),
    Element("div",List(Element("pre",List(),List(),List())),List(WebAttribute("src","http")),List(WebStyle("display","none"), WebStyle("width","100px"), WebStyle("height","100px")))
  )
  reverseInit.toList shouldEqual List((initArg1, initArg2))
  
  // Last element changed
  val reverseInit2 = WebElementAddition.applyRev((Element("div", Nil, Nil, List(WebStyle("display", "none"))), (List(Element("pre")), List(WebAttribute("src", "http")), List(WebStyle("width", "100px"), WebStyle("height", "100px")))),
    Element("div",List(Element("pre",List(),List(),List())),List(WebAttribute("src","http")),List(WebStyle("display","none"), WebStyle("width","100px"), WebStyle("height","200px")))
  )
  reverseInit2.toList shouldEqual List((Element("div",List(),List(),List(WebStyle("display","none"))),(List(Element("pre",List(),List(),List())),List(WebAttribute("src","http")),List(WebStyle("width","100px"), WebStyle("height","200px")))))
  
  // Added a child at the beginning
  val reverseInit3 = WebElementAddition.applyRev((Element("div", Nil, Nil, List(WebStyle("display", "none"))), (List(Element("pre")), List(WebAttribute("src", "http")), List(WebStyle("width", "100px"), WebStyle("height", "100px")))),
    Element("div",List(Element("pre",List(),List(),List()), Element("span",List(),List(),List())),List(WebAttribute("src","http")),List(WebStyle("display","none"), WebStyle("width","100px"), WebStyle("height","200px")))
  )
  reverseInit3.toList shouldEqual List((Element("div",List(),List(),List(WebStyle("display","none"))),(List(Element("pre",List(),List(),List()), Element("span",List(),List(),List())),List(WebAttribute("src","http")),List(WebStyle("width","100px"), WebStyle("height","200px")))))
  
  // Changed the display
  val reverseInit4 = WebElementAddition.applyRev((Element("div", Nil, Nil, List(WebStyle("display", "none"))), (List(Element("pre")), List(WebAttribute("src", "http")), List(WebStyle("width", "100px"), WebStyle("height", "100px")))),
    Element("div",List(Element("pre",List(),List(),List())),List(WebAttribute("src","http")),List(WebStyle("display","block"), WebStyle("width","100px"), WebStyle("height","100px")))
  )
  reverseInit4.toList shouldEqual List((Element("div",List(),List(),List(WebStyle("display","block"))),(List(Element("pre",List(),List(),List())), List(WebAttribute("src","http")),List(WebStyle("width","100px"), WebStyle("height","100px")))))
  
  // Added a style before the original style
  val reverseInit5 = WebElementAddition.applyRev((Element("div", Nil, Nil, List(WebStyle("display", "none"))), (List(Element("pre")), List(WebAttribute("src", "http")), List(WebStyle("width", "100px"), WebStyle("height", "100px")))),
    Element("div",List(Element("pre",List(),List(),List())),List(WebAttribute("src","http")),List(WebStyle("outline","1px solid black"), WebStyle("display","none"), WebStyle("width","100px"), WebStyle("height","100px")))
  )
  reverseInit5.toList shouldEqual List((Element("div",List(),List(),List(WebStyle("outline","1px solid black"), WebStyle("display","none"))),(List(Element("pre",List(),List(),List())), List(WebAttribute("src","http")),List(WebStyle("width","100px"), WebStyle("height","100px")))))
}

class WebElementCompositionTest extends FunSuite  {
  import TypeSplit._
  import WebElementComposition._
  test("should compose and decompose elements correctly") {
    val initArg1 = Element("div", Nil, Nil, List(WebStyle("display", "none")))
    val initArg2 = List(WebStyle("width", "100px"), Element("pre"), WebStyle("height", "100px"), WebAttribute("src", "http"))
    val in = (initArg1, initArg2)
    val sinit = WebElementComposition.get(in)
    // Verification that the function computes correctly
    sinit shouldEqual Element("div", List(Element("pre")), List(WebAttribute("src", "http")), List(WebStyle("display", "none"), WebStyle("width", "100px"), WebStyle("height", "100px")))
    // Replacing an element in the argument's list.
    WebElementComposition.put(Element("div", List(Element("span")), List(WebAttribute("src", "http")), List(WebStyle("display", "none"), WebStyle("width", "100px"), WebStyle("height", "100px"))), in).toList shouldEqual List((initArg1, initArg2.updated(1, Element("span"))))
    // Adding an element at the end of the argument's list.
    WebElementComposition.put(Element("div", List(Element("pre"), Element("span")), List(WebAttribute("src", "http")), List(WebStyle("display", "none"), WebStyle("width", "100px"), WebStyle("height", "100px"))), in).toList shouldEqual List((initArg1, List(WebStyle("width", "100px"), Element("pre"), WebStyle("height", "100px"), WebAttribute("src", "http"), Element("span"))))
    // Adding an element before one of the argument's list.
    val r = WebElementComposition.put(Element("div", List(Element("span"), Element("pre")), List(WebAttribute("src", "http")), List(WebStyle("display", "none"), WebStyle("width", "100px"), WebStyle("height", "100px"))), in).toList 
    r should contain ((initArg1, List(WebStyle("width", "100px"), Element("span"), Element("pre"), WebStyle("height", "100px"), WebAttribute("src", "http"))))
    r should have size 2
    // Replacing the main element
    WebElementComposition.put(Element("div", List(Element("pre")), List(WebAttribute("src", "http")), List(WebStyle("display", "block"), WebStyle("width", "100px"), WebStyle("height", "100px"))), in).toList shouldEqual List((initArg1.copy(styles=List(WebStyle("display", "block"))), initArg2))
  }
}

class ComposeTest extends FunSuite  {
  
  object F extends ~~>[Int, Int] {
    def get(x: Int) = x - (x % 2)
    def put(x: Int, in: Option[Int]) = if(x % 2 == 0) List(x, x+1) else Nil
  }

  object G extends ~~>[Int, Int]  {
    def get(x: Int) = x - (x % 3)
    def put(x: Int, in: Option[Int]) = if(x % 3 == 0) List(x, x+1, x+2) else Nil
  }

  val b = Compose(G, F)

  def composeRev(i: Int) = b.put(i, 0).toList

  test("Reverse composing of functions") {
    val test1 = composeRev(0) shouldEqual List(0, 1, 2, 3)
    val test2 = composeRev(3) shouldEqual List(4, 5)
    val test3 = composeRev(6) shouldEqual List(6, 7, 8, 9)
  }
}

class FlattenTest extends FunSuite  {
  val c = new Flatten[Int]
  import c._

  test("Reversing Flatten") {
    flattenRev(List(List(1, 2, 3), List(5, 6), List(), List(7)), List(1, 2, 3, 5, 6, 7)) should contain 
      List(List(1, 2, 3), List(5, 6), List(), List(7))
    val test2 = flattenRev(List(List(1, 2, 3), List(5, 6), List(), List(7)), List(1, 2, 5, 6, 7)) should contain  
      List(List(1, 2), List(5, 6), List(), List(7))
    val test3 = flattenRev(List(List(1, 2, 3), List(5, 6), List(), List(7)), List(1, 3, 5, 6, 7)) should 
    contain (List(List(1, 3), List(5, 6), List(), List(7))) //'
    val test4 = flattenRev(List(List(1, 2, 3), List(5, 6), List(), List(7)), List(1, 2, 3, 4, 5, 6, 7)) should contain  
      List(List(1, 2, 3), List(4, 5, 6), List(), List(7))
    val test5 = flattenRev(List(List(1, 2, 3), List(5, 6), List(), List(7)), List(1, 2, 4, 3, 5, 6, 7)) should contain  
      List(List(1, 2, 4, 3), List(5, 6), List(), List(7))
    val test6 = flattenRev(List(List(1, 2, 3), List(5, 6), List(), List(7)), List(1, 2, 3, 5, 6, 4, 7)) should contain  
      List(List(1, 2, 3), List(5, 6), List(), List(4, 7))
    val test7 = flattenRev(List(List(1, 2, 3), List(5, 6), List(), List(7)), List(1, 2, 3, 5, 6, 7, 4)) should contain  
      List(List(1, 2, 3), List(5, 6), List(), List(7, 4))
  }
}

class MapReverseTest extends FunSuite  {
  object f extends ~~>[Int, Int] {
    def get(x: Int) = x - (x%2)
    def put(y: Int, in: Option[Int]) =
      if(y % 2 == 0) {
        in match {
          case Some(x) if get(x) == y => List(x)
          case _ =>
           List(y, y+1)
        }
      } else Nil
  }
  val c = MapReverse[Int, Int](f)
  import c._
  test("Reversing map") {
    put(List(0, 2, 2, 4, 4), List(1, 2, 3, 4, 5)) shouldEqual
    List(List(1, 2, 3, 4, 5))
    put(List(0, 4, 2, 4, 4), List(1, 2, 3, 4, 5)) shouldEqual
    List(List(1, 4, 3, 4, 5), List(1, 5, 3, 4, 5))
    put(List(0, 2, 4, 4), List(1, 2, 3, 4, 5)) should contain
    (List(1, 2, 4, 5)) //'
    put(List(0, 2, 2, 2, 4, 4), List(1, 2, 3, 4, 5)) shouldEqual
    List(List(1, 2, 3, 2, 4, 5), List(1, 2, 3, 3, 4, 5))
  }
}

class FilterReverseTest extends FunSuite  {
  val isEven = (x: Int) => x % 2 == 0
  val c = FilterReverse(isEven)
  test("Filter reverse") {
    import c.put
    put(List(2, 4, 8), List(1, 2, 3, 4, 8, 5)) shouldEqual
    List(List(1, 2, 3, 4, 8, 5))
    put(List(2, 8), List(1, 2, 3, 4, 8, 5)) shouldEqual
    List(List(1, 2, 3, 8, 5))
    put(List(4, 8), List(1, 2, 3, 4, 8, 5)) shouldEqual
    List(List(1, 3, 4, 8, 5))
    put(List(2, 4, 6, 8), List(1, 2, 3, 4, 8, 5)) shouldEqual
    List(List(1, 2, 3, 4, 6, 8, 5))
    put(List(2, 6, 4, 8), List(1, 2, 3, 4, 8, 5)) shouldEqual
    List(List(1, 2, 3, 6, 4, 8, 5))
  }
  
  test("Filter reverse with strings") {
    val d = FilterReverse((s: String) => s.startsWith("S"))
    import d.put
    put(List("Salami", "Sudjuk"), List("Margharita", "Sudjuk")).toList should contain (List("Margharita", "Salami", "Sudjuk"))
  }
}

// Combines map and flatten directly.
class FlatMapByComposeTest extends FunSuite  {
  object f extends ~~>[Int, List[Int]] {
    def get(x: Int) = if(x % 4 == 0) List(x, x+1, x+2) else if(x % 4 == 2) List(x+1, x+2) else if(x % 4 == 1) List(x-1, x) else List(x-1, x, x+1)
    def put(lx: List[Int], in: Option[Int]) = if(lx.length == 3 && lx(1) == lx(0) + 1 && lx(2) == lx(1) + 1) {
      if(lx(0) % 4 == 0) List(lx(0))
      else if(lx(0) % 4 == 2) List(lx(1))
      else Nil
    } else if(lx.length == 2 && lx(1) == lx(0) + 1) {
      if(lx(0) % 4 == 3) List(lx(0)-1)
      else if(lx(0) % 4 == 0) List(lx(1))
      else Nil
    } else Nil
  }

  val c = MapReverse(f) andThen Flatten[Int]()
  
  // f(0) ++ f(2) == f(1) ++ f(3)
  // f(0) == [0, 1, 2]
  // f(1) == [0, 1]
  // f(2) == [3, 4]
  // f(3) == [2, 3, 4]
  
  object fEven extends ~~>[Int, List[Int]] {
     def get(x: Int) = if(x%2 == 0) List(x/2) else Nil
     def put(x: List[Int], in: Option[Int]) = if(x.length == 1) List(x(0)*2) else if(x.length == 0 && in.nonEmpty) List(in.get) else Nil
  }
 
  val d = MapReverse(fEven) andThen Flatten[Int]()

  test("Reverse flatmap - complicated") {
    import c.put
    Flatten[Int]().put(List(0, 1, 2, 3, 4), Some(Nil)) should contain (List(List(0, 1, 2), List(3, 4)))
    put(List(0, 1, 2, 3, 4), Nil) shouldEqual List(List(1, 3), List(0, 2))
    put(List(0, 1, 2, 3, 4), List(1, 3)) should contain(List(1, 3))
    put(List(0, 1, 2, 3, 4), List(0, 2)) should contain(List(0, 2))
    put(List(0, 1, 2, 3, 4, 0, 1), List(0, 2)) should contain(List(0, 2, 1)) // Addition at the end
    put(List(0, 1, 2, 0, 1, 3, 4), List(0, 2)) should contain(List(0, 1, 2)) // Addition in the middle
    put(List(0, 1, 0, 1, 2, 3, 4), List(0, 2)) should contain(List(1, 0, 2)) // Addition at the beg.
    put(List(3, 4), List(0, 2)) should contain(List(2)) // Deletion of beginning
    put(List(0, 1, 2), List(0, 2)) should contain(List(0)) // Deletion of end
    put(List(2, 3, 4), List(2)) should contain(List(3)) // Change
    put(List(0, 1, 2, 0, 1, 2, 3, 4), List(0, 1, 2)) should contain(List(0, 1, 3)) // Change
    put(List(0, 1, 0, 1, 2, 3, 4), List(1, 3)) should contain(List(1, 1, 3)) // Addition at beg.
  }
  test("Reverse flatmap - even") {
    import d.put

    // Keep elements producing empty lists
    put(List(1, 2), List(1, 2, 3, 4, 5)) should contain(List(1, 2, 3, 4, 5))
    put(List(1, 3, 2), List(1, 2, 3, 4, 5)) should contain(List(1, 2, 3, 6, 4, 5))
    put(List(1, 2), List(1, 2, 3, 6, 4, 5)) should contain(List(1, 2, 3, 4, 5))
  }
}

// Combines map and flatten directly.
class FlatMapTest extends FunSuite  {
  object f extends ~~>[Int, List[Int]] {
    def get(x: Int) = if(x % 4 == 0) List(x, x+1, x+2) else if(x % 4 == 2) List(x+1, x+2) else if(x % 4 == 1) List(x-1, x) else List(x-1, x, x+1)
    def put(lx: List[Int], in: Option[Int]) = if(lx.length == 3 && lx(1) == lx(0) + 1 && lx(2) == lx(1) + 1) {
      if(lx(0) % 4 == 0) List(lx(0))
      else if(lx(0) % 4 == 2) List(lx(1))
      else Nil
    } else if(lx.length == 2 && lx(1) == lx(0) + 1) {
      if(lx(0) % 4 == 3) List(lx(0)-1)
      else if(lx(0) % 4 == 0) List(lx(1))
      else Nil
    } else Nil
  }

  val c = FlatMap(f)
  
  // f(0) ++ f(2) == f(1) ++ f(3)
  // f(0) == [0, 1, 2]
  // f(1) == [0, 1]
  // f(2) == [3, 4]
  // f(3) == [2, 3, 4]
  
  object fEven extends ~~>[Int, List[Int]] {
     def get(x: Int) = if(x%2 == 0) List(x/2) else Nil
     def put(x: List[Int], in: Option[Int]) = if(x.length == 1) List(x(0)*2) else Nil
  }
 
  val d = FlatMap(fEven)

  test("Reverse flatmap - complicated") {
    import c.put
    put(List(0, 1, 2, 3, 4), Nil) shouldEqual List(List(1, 3), List(0, 2))
    put(List(0, 1, 2, 3, 4), List(1, 3)) shouldEqual List(List(1, 3))
    put(List(0, 1, 2, 3, 4), List(0, 2)) shouldEqual List(List(0, 2))
    put(List(0, 1, 2, 3, 4, 0, 1), List(0, 2)) shouldEqual List(List(0, 2, 1)) // Addition at the end
    put(List(0, 1, 2, 0, 1, 3, 4), List(0, 2)) shouldEqual List(List(0, 1, 2)) // Addition in the middle
    put(List(0, 1, 0, 1, 2, 3, 4), List(0, 2)) shouldEqual List(List(1, 0, 2)) // Addition at the beg.
    put(List(3, 4), List(0, 2)) shouldEqual List(List(2)) // Deletion of beginning
    put(List(0, 1, 2), List(0, 2)) shouldEqual List(List(0)) // Deletion of end
    put(List(2, 3, 4), List(2)) shouldEqual List(List(3)) // Change
    put(List(0, 1, 2, 0, 1, 2, 3, 4), List(0, 1, 2)) shouldEqual List(List(0, 1, 3)) // Change
    put(List(0, 1, 0, 1, 2, 3, 4), List(1, 3)) shouldEqual List(List(1, 1, 3)) // Addition at beg.
  }
  test("Reverse flatmap - even") {
    import d.put
    // Keep elements producing empty lists
    put(List(1, 2), List(1, 2, 3, 4, 5)) shouldEqual List(List(1, 2, 3, 4, 5))
    put(List(1, 3, 2), List(1, 2, 3, 4, 5)) shouldEqual List(List(1, 2, 3, 6, 4, 5))
    put(List(1, 2), List(1, 2, 3, 6, 4, 5)) shouldEqual List(List(1, 2, 3, 4, 5))
  }
}

class PairTest extends FunSuite {
  object f extends ~~>[Int, Int] {
    def get(x: Int) = x - (x%2)
    def put(y: Int, in: Option[Int]) =
      if(y % 2 == 0) {
        in match {
          case Some(x) if get(x) == y => List(x)
          case _ =>
           List(y, y+1)
        }
      } else Nil
  }
  
  val c = Pair(f, f)

  test("Reverse pair") {
    c.get((0, 3)) shouldEqual ((0, 2))
    c.put((0, 2)).toList.sorted shouldEqual (List((0, 2), (0, 3), (1, 2), (1, 3)))
    c.put((0, 2), Some((0, 3))).toList.sorted shouldEqual (List((0, 3))) 
  }
}

class PizzaTest extends FunSuite {
   import WebBuilder._
   import Implicits.{RemoveUnit => _, _}
   /*object TN extends (String ~~> List[Tree]) {
     def get(s: String) = List(TextNode(s))
     def put(out: List[Tree], s: Option[String]): Iterable[String] = report(s"TN.put($s, $out) = %s"){
       out match {
       case List(TextNode(i)) => List(i)
       case _ => Nil
     }
   }
   }
   val pizzasCreator: (List[String] ~~> Element) =
     (<.ul(
       MapReverse(<.li(TN)): (List[String] ~~> List[Element])
     ): ((Unit, List[String]) ~~> Element))
   test("It can creat pizzas forms") {
     pizzasCreator.get(List("Margharita", "Sudjuk")).toString shouldEqual
      """<.ul(<.li("Margharita"), <.li("Sudjuk"))"""
   }
   test("It can find pizzas from an updated list of pizzas") {
     val expectedResult = Element("ul", Element("li", TextNode("Margharita")::Nil)::Element("li", TextNode("Salami")::Nil)::Element("li", TextNode("Sudjuk")::Nil)::Nil)
     val original = List("Margharita", "Sudjuk")
     pizzasCreator.put(expectedResult, Some(original)) should contain (
     List("Margharita", "Salami", "Sudjuk"))
   }
   val pizzasCreator2: (List[String] ~~> Element) =
     FilterReverse((s: String) => s.startsWith("S")) andThen (<.ul(
       MapReverse(<.li(TN)): (List[String] ~~> List[Element])
     ): ((Unit, List[String]) ~~> Element))
   test("it can deal with filters") {
     val expectedResult = Element("ul", Element("li", TextNode("Salami")::Nil)::Element("li", TextNode("Sudjuk")::Nil)::Nil)
     val original = List("Margharita", "Sudjuk")
     pizzasCreator2.put(expectedResult, Some(original)) should contain (
     List("Margharita", "Salami", "Sudjuk"))
   }
   */
   val ul = Element("ul")
   val li = Element("li")

   def pizzasCreator3Raw(l: List[String]) = {
     val filtered = l.filter((s: String)=> s.startsWith("S"))
     val mapped = filtered.map((x: String) => li(List(TextNode(x))))
     val result = ul(mapped)
     result
   }
   
   def pizzasCreator3(l: Id[List[String]]) = {
     val filtered = l.filter((s: String)=> s.startsWith("S"))
     val mapped = filtered.map((x: Id[String]) => li(List(CastUp[String, TextNode, Tree](TextNode(x)))))
     val result = ul(mapped)
     result
   }
   test("it can use standard methods") {
     val expectedResult = Element("ul", Element("li", TextNode("Salami")::Nil)::Element("li", TextNode("Sudjuk")::Nil)::Nil)
     val original = List("Margharita", "Sudjuk")
     pizzasCreator3Raw(original) shouldEqual Element("ul", Element("li", TextNode("Sudjuk")::Nil)::Nil)
     pizzasCreator3(Id()).get(original) shouldEqual Element("ul", Element("li", TextNode("Sudjuk")::Nil)::Nil)
     pizzasCreator3(Id()).put(expectedResult, Some(original)) should contain (
     List("Margharita", "Salami", "Sudjuk"))
   }
}

/**
This test focuses on the task of updating the result containing the duplication of an object.
It tests that the object which was not there before is given the priority to represent all the changes.
*/
class DuplicateTest extends FunSuite {
   import WebBuilder._
   import Implicits.{RemoveUnit => _, _}
   
   def duplicate(d: WebElement) = 
     Element("div", d::d::Nil)
   def duplicate2(d: Id[WebElement]) =
     Element("div", d::d::Nil)
     
   test("it can duplicate and un-duplicate") {
     duplicate(Element("pre")) shouldEqual Element("div", Element("pre")::Element("pre")::Nil)
     duplicate2(Id()).get(Element("pre")) shouldEqual Element("div", Element("pre")::Element("pre")::Nil)
     duplicate2(Id()).put(Element("div", Element("span")::Element("span")::Nil)) should contain (Element("span"))
   }
   
   test("it can un-duplicate partially") {
     duplicate2(Id()).put(Element("div", Element("span")::Element("pre")::Nil), Some(Element("span"))).toList shouldEqual (List(Element("pre")))
     duplicate2(Id()).put(Element("div", Element("span")::Element("pre")::Nil), Some(Element("pre"))).toList shouldEqual (List(Element("span")))
     duplicate2(Id()).put(Element("div", Element("br")::Element("pre")::Nil), Some(Element("span"))).toList shouldEqual (List(Element("br"), Element("pre")))
     //duplicate2(Id()).put(Element("div", Element("br")::Element("pre")::Element("span")::Nil), Some(Element("span"))).toList shouldEqual (List(Element("br"), Element("pre")))
   }
}

class ReproduceTest extends FunSuite {
   import WebBuilder._
   import Implicits.{RemoveUnit => _, _}
   
   def reproduce(d: (Int, WebElement)) = 
     Element("div", List.fill(d._1)(d._2))
   def reproduce2(d: Id[(Int, WebElement)]): ((Int, WebElement) ~~> Element) =
     Element("div", Listfill(d))
     
   test("it can reproduce and un-reproduce") {
     reproduce((3, Element("pre"))) shouldEqual Element("div", Element("pre")::Element("pre")::Element("pre")::Nil)
     reproduce2(Id()).get((3, Element("pre"))) shouldEqual Element("div", Element("pre")::Element("pre")::Element("pre")::Nil)
     reproduce2(Id()).put(Element("div", Element("span")::Element("span")::Nil)).toList shouldEqual (List((2, Element("span"))))
   }
   
   test("it can un-reproduce partially") {
     reproduce2(Id()).put(Element("div", Element("span")::Element("pre")::Nil)).toList shouldEqual (List((2, Element("span")), (2, Element("pre"))))
     reproduce2(Id()).put(Element("div", Element("span")::Element("pre")::Nil), (2, Element("pre"))).toList shouldEqual
       (List((2, Element("span"))))
     reproduce2(Id()).put(Element("div", Element("span")::Element("pre")::Nil), (3, Element("pre"))).toList shouldEqual
       (List((2, Element("span"))))
     reproduce2(Id()).put(Element("div", Element("pre")::Element("pre")::Element("span")::Nil), (2, Element("pre"))).toList shouldEqual
       (List((3, Element("span"))))
   }
}

/**
Future work: If cannot revert a function, abstract it using one more argument !

*/