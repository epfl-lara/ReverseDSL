import org.scalatest._
import shapeless.syntax.zipper._
import Matchers._

class StringAppendTest extends FunSuite {
  import StringAppend.{unperform => appendRev, _}
  def f = append(append("Hello", " "), "world")
  def fRev(out: String): List[(String, String, String)] = appendRev(("Hello ", "world"), out).toList.flatMap(leftRight => 
    appendRev(("Hello", " "), leftRight._1).map(lr => (lr._1, lr._2, leftRight._2))
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
  }
}

class StringFormatReverseTest extends FunSuite  {
  import StringFormatReverse._
  test("Formatting reverse decomposition") {
    formatRev("%s %s %d", List("Hello", "world", 42), "Hello buddy 42") shouldEqual List(("%s %s %d", List("Hello", "buddy", 42)))
    formatRev("%s,%s %s!", List("Hello", "obscure", "world"), "Hello, obscure world!") should contain (("%s, %s %s!", List("Hello", "obscure", "world")))
    formatRev("%s,%s %s!", List("Hello", "obscure", "world"), "Hello,clear world!") should contain (("%s,%s %s!", List("Hello", "clear", "world")))
    formatRev("%s,%s %s!", List("Hello", "obscure", "world"), "Good bye,awesome friend!") should contain (("%s,%s %s!", List("Good bye", "awesome", "friend")))
    formatRev("%2$s,%3$s %1$s!", List("world", "Hello", "obscure"), "Hello,clear world!") should contain (("%2$s,%3$s %1$s!", List("world", "Hello", "clear")))
    formatRev("Hello %1$s! %1$s is ok?", List("Marion"), "Hello Mikael! Marion is ok?") should contain(("Hello %1$s! %1$s is ok?", List("Mikael")))
    formatRev("Hello %1$s! %1$s is ok?", List("Marion"), "Hello Mikael! Marion is ok?") should not contain (("Hello %1$s! %1$s is ok?", List("Marion")))
  }
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
    val initTest = List(WebStyle("width", "100px"), WebElement("pre"), WebStyle("height", "100px"), WebAttribute("src", "http"))
    
    val sinit = split(initTest)

    splitRev(initTest, (sinit._1, sinit._2, sinit._3(0) :: WebStyle("outline", "bold") :: sinit._3(1) :: Nil)) shouldEqual
    List(List(WebStyle("width","100px"), WebElement("pre"), WebStyle("outline","bold"), WebStyle("height","100px"), WebAttribute("src","http")))
    splitRev(initTest, (sinit._1, sinit._2, sinit._3(0) :: Nil)) shouldEqual
    List(List(WebStyle("width","100px"), WebElement("pre"), WebAttribute("src","http")))
  }
}

class WebElementAdditionTest extends FunSuite  {
  import TypeSplit._
  import WebElementAddition._
  val initArg1 = WebElement("div", Nil, Nil, List(WebStyle("display", "none")))
  val initArg2 = (List(WebElement("pre")), List(WebAttribute("src", "http")), List(WebStyle("width", "100px"), WebStyle("height", "100px")))
  val sinit = WebElementAddition(initArg1, initArg2._1, initArg2._2, initArg2._3)
  
  // No modification
  val reverseInit = WebElementAddition.applyRev((WebElement("div", Nil, Nil, List(WebStyle("display", "none"))), (List(WebElement("pre")), List(WebAttribute("src", "http")), List(WebStyle("width", "100px"), WebStyle("height", "100px")))),
    WebElement("div",List(WebElement("pre",List(),List(),List())),List(WebAttribute("src","http")),List(WebStyle("display","none"), WebStyle("width","100px"), WebStyle("height","100px")))
  )
  reverseInit.toList shouldEqual List((initArg1, initArg2))
  
  // Last element changed
  val reverseInit2 = WebElementAddition.applyRev((WebElement("div", Nil, Nil, List(WebStyle("display", "none"))), (List(WebElement("pre")), List(WebAttribute("src", "http")), List(WebStyle("width", "100px"), WebStyle("height", "100px")))),
    WebElement("div",List(WebElement("pre",List(),List(),List())),List(WebAttribute("src","http")),List(WebStyle("display","none"), WebStyle("width","100px"), WebStyle("height","200px")))
  )
  reverseInit2.toList shouldEqual List((WebElement("div",List(),List(),List(WebStyle("display","none"))),(List(WebElement("pre",List(),List(),List())),List(WebAttribute("src","http")),List(WebStyle("width","100px"), WebStyle("height","200px")))))
  
  // Added a child at the beginning
  val reverseInit3 = WebElementAddition.applyRev((WebElement("div", Nil, Nil, List(WebStyle("display", "none"))), (List(WebElement("pre")), List(WebAttribute("src", "http")), List(WebStyle("width", "100px"), WebStyle("height", "100px")))),
    WebElement("div",List(WebElement("pre",List(),List(),List()), WebElement("span",List(),List(),List())),List(WebAttribute("src","http")),List(WebStyle("display","none"), WebStyle("width","100px"), WebStyle("height","200px")))
  )
  reverseInit3.toList shouldEqual List((WebElement("div",List(),List(),List(WebStyle("display","none"))),(List(WebElement("pre",List(),List(),List()), WebElement("span",List(),List(),List())),List(WebAttribute("src","http")),List(WebStyle("width","100px"), WebStyle("height","200px")))))
  
  // Changed the display
  val reverseInit4 = WebElementAddition.applyRev((WebElement("div", Nil, Nil, List(WebStyle("display", "none"))), (List(WebElement("pre")), List(WebAttribute("src", "http")), List(WebStyle("width", "100px"), WebStyle("height", "100px")))),
    WebElement("div",List(WebElement("pre",List(),List(),List())),List(WebAttribute("src","http")),List(WebStyle("display","block"), WebStyle("width","100px"), WebStyle("height","100px")))
  )
  reverseInit4.toList shouldEqual List((WebElement("div",List(),List(),List(WebStyle("display","block"))),(List(WebElement("pre",List(),List(),List())), List(WebAttribute("src","http")),List(WebStyle("width","100px"), WebStyle("height","100px")))))
  
  // Added a style before the original style
  val reverseInit5 = WebElementAddition.applyRev((WebElement("div", Nil, Nil, List(WebStyle("display", "none"))), (List(WebElement("pre")), List(WebAttribute("src", "http")), List(WebStyle("width", "100px"), WebStyle("height", "100px")))),
    WebElement("div",List(WebElement("pre",List(),List(),List())),List(WebAttribute("src","http")),List(WebStyle("outline","1px solid black"), WebStyle("display","none"), WebStyle("width","100px"), WebStyle("height","100px")))
  )
  reverseInit5.toList shouldEqual List((WebElement("div",List(),List(),List(WebStyle("outline","1px solid black"), WebStyle("display","none"))),(List(WebElement("pre",List(),List(),List())), List(WebAttribute("src","http")),List(WebStyle("width","100px"), WebStyle("height","100px")))))
}

class WebElementCompositionTest extends FunSuite  {
  import TypeSplit._
  import WebElementComposition._
  test("should compose and decompose elements correctly") {
    val initArg1 = WebElement("div", Nil, Nil, List(WebStyle("display", "none")))
    val initArg2 = List(WebStyle("width", "100px"), WebElement("pre"), WebStyle("height", "100px"), WebAttribute("src", "http"))
    val in = (initArg1, initArg2)
    val sinit = WebElementComposition.perform(in)
    // Verification that the function computes correctly
    sinit shouldEqual WebElement("div", List(WebElement("pre")), List(WebAttribute("src", "http")), List(WebStyle("display", "none"), WebStyle("width", "100px"), WebStyle("height", "100px")))
    // Replacing an element in the argument's list.
    WebElementComposition.unperform(in, WebElement("div", List(WebElement("span")), List(WebAttribute("src", "http")), List(WebStyle("display", "none"), WebStyle("width", "100px"), WebStyle("height", "100px")))).toList shouldEqual List((initArg1, initArg2.updated(1, WebElement("span"))))
    // Adding an element at the end of the argument's list.
    WebElementComposition.unperform(in, WebElement("div", List(WebElement("pre"), WebElement("span")), List(WebAttribute("src", "http")), List(WebStyle("display", "none"), WebStyle("width", "100px"), WebStyle("height", "100px")))).toList shouldEqual List((initArg1, List(WebStyle("width", "100px"), WebElement("pre"), WebStyle("height", "100px"), WebAttribute("src", "http"), WebElement("span"))))
    // Adding an element before one of the argument's list.
    val r = WebElementComposition.unperform(in, WebElement("div", List(WebElement("span"), WebElement("pre")), List(WebAttribute("src", "http")), List(WebStyle("display", "none"), WebStyle("width", "100px"), WebStyle("height", "100px")))).toList 
    r should contain ((initArg1, List(WebStyle("width", "100px"), WebElement("span"), WebElement("pre"), WebStyle("height", "100px"), WebAttribute("src", "http"))))
    r should have size 2
    // Replacing the main element
    WebElementComposition.unperform(in, WebElement("div", List(WebElement("pre")), List(WebAttribute("src", "http")), List(WebStyle("display", "block"), WebStyle("width", "100px"), WebStyle("height", "100px")))).toList shouldEqual List((initArg1.copy(styles=List(WebStyle("display", "block"))), initArg2))
  }
}

class ComposeTest extends FunSuite  {
  
  object F extends ~~>[Int, Int] {
    def perform(x: Int) = x - (x % 2)
    def unperform(in: Option[Int], x: Int) = if(x % 2 == 0) List(x, x+1) else Nil
  }

  object G extends ~~>[Int, Int]  {
    def perform(x: Int) = x - (x % 3)
    def unperform(in: Option[Int], x: Int) = if(x % 3 == 0) List(x, x+1, x+2) else Nil
  }

  val b = Compose(G, F)

  def composeRev(i: Int) = b.unperform(0, i).toList

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
    def perform(x: Int) = x - (x%2)
    def unperform(in: Option[Int], x: Int) =
      if(x % 2 == 0) List(x, x+1) else Nil
  }
  val c = MapReverse[Int, Int](f)
  import c._
  test("Reversing map") {
    unperform(List(1, 2, 3, 4, 5), List(0, 2, 2, 4, 4)) shouldEqual
    List(List(1, 2, 3, 4, 5))
    unperform(List(1, 2, 3, 4, 5), List(0, 4, 2, 4, 4)) shouldEqual
    List(List(1, 4, 3, 4, 5), List(1, 5, 3, 4, 5))
    unperform(List(1, 2, 3, 4, 5), List(0, 2, 4, 4)) should contain
    (List(1, 2, 4, 5)) //'
    unperform(List(1, 2, 3, 4, 5), List(0, 2, 2, 2, 4, 4)) shouldEqual
    List(List(1, 2, 3, 2, 4, 5), List(1, 2, 3, 3, 4, 5))
  }
}

class FilterReverseTest extends FunSuite  {
  val isEven = (x: Int) => x % 2 == 0
  val c = FilterReverse(isEven)
  import c.unperform
  test("Filter reverse") {
    unperform(List(1, 2, 3, 4, 8, 5), List(2, 4, 8)) shouldEqual
    List(List(1, 2, 3, 4, 8, 5))
    unperform(List(1, 2, 3, 4, 8, 5), List(2, 8)) shouldEqual
    List(List(1, 2, 3, 8, 5))
    unperform(List(1, 2, 3, 4, 8, 5), List(4, 8)) shouldEqual
    List(List(1, 3, 4, 8, 5))
    unperform(List(1, 2, 3, 4, 8, 5), List(2, 4, 6, 8)) shouldEqual
    List(List(1, 2, 3, 4, 6, 8, 5))
    unperform(List(1, 2, 3, 4, 8, 5), List(2, 6, 4, 8)) shouldEqual
    List(List(1, 2, 3, 6, 4, 8, 5))
  }
}

// Combines map and flatten directly.
class FlatMapByComposeTest extends FunSuite  {
  object f extends ~~>[Int, List[Int]] {
    def perform(x: Int) = if(x % 4 == 0) List(x, x+1, x+2) else if(x % 4 == 2) List(x+1, x+2) else if(x % 4 == 1) List(x-1, x) else List(x-1, x, x+1)
    def unperform(in: Option[Int], lx: List[Int]) = if(lx.length == 3 && lx(1) == lx(0) + 1 && lx(2) == lx(1) + 1) {
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
     def perform(x: Int) = if(x%2 == 0) List(x/2) else Nil
     def unperform(in: Option[Int], x: List[Int]) = if(x.length == 1) List(x(0)*2) else if(x.length == 0 && in.nonEmpty) List(in.get) else Nil
  }
 
  val d = MapReverse(fEven) andThen Flatten[Int]()

  test("Reverse flatmap - complicated") {
    import c.unperform
    Flatten[Int]().unperform(Some(Nil), List(0, 1, 2, 3, 4)) should contain (List(List(0, 1, 2), List(3, 4)))
    unperform(Nil, List(0, 1, 2, 3, 4)) shouldEqual List(List(1, 3), List(0, 2))
    unperform(List(1, 3), List(0, 1, 2, 3, 4)) should contain(List(1, 3))
    unperform(List(0, 2), List(0, 1, 2, 3, 4)) should contain(List(0, 2))
    unperform(List(0, 2), List(0, 1, 2, 3, 4, 0, 1)) should contain(List(0, 2, 1)) // Addition at the end
    unperform(List(0, 2), List(0, 1, 2, 0, 1, 3, 4)) should contain(List(0, 1, 2)) // Addition in the middle
    unperform(List(0, 2), List(0, 1, 0, 1, 2, 3, 4)) should contain(List(1, 0, 2)) // Addition at the beg.
    unperform(List(0, 2), List(3, 4)) should contain(List(2)) // Deletion of beginning
    unperform(List(0, 2), List(0, 1, 2)) should contain(List(0)) // Deletion of end
    unperform(List(2), List(2, 3, 4)) should contain(List(3)) // Change
    unperform(List(0, 1, 2), List(0, 1, 2, 0, 1, 2, 3, 4)) should contain(List(0, 1, 3)) // Change
    unperform(List(1, 3), List(0, 1, 0, 1, 2, 3, 4)) should contain(List(1, 1, 3)) // Addition at beg.
  }
  test("Reverse flatmap - even") {
    import d.unperform

    // Keep elements producing empty lists
    unperform(List(1, 2, 3, 4, 5), List(1, 2)) should contain(List(1, 2, 3, 4, 5))
    unperform(List(1, 2, 3, 4, 5), List(1, 3, 2)) should contain(List(1, 2, 3, 6, 4, 5))
    unperform(List(1, 2, 3, 6, 4, 5), List(1, 2)) should contain(List(1, 2, 3, 4, 5))
  }
}

// Combines map and flatten directly.
class FlatMapTest extends FunSuite  {
  object f extends ~~>[Int, List[Int]] {
    def perform(x: Int) = if(x % 4 == 0) List(x, x+1, x+2) else if(x % 4 == 2) List(x+1, x+2) else if(x % 4 == 1) List(x-1, x) else List(x-1, x, x+1)
    def unperform(in: Option[Int], lx: List[Int]) = if(lx.length == 3 && lx(1) == lx(0) + 1 && lx(2) == lx(1) + 1) {
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
     def perform(x: Int) = if(x%2 == 0) List(x/2) else Nil
     def unperform(in: Option[Int], x: List[Int]) = if(x.length == 1) List(x(0)*2) else Nil
  }
 
  val d = FlatMap(fEven)

  test("Reverse flatmap - complicated") {
    import c.unperform
    unperform(Nil, List(0, 1, 2, 3, 4)) shouldEqual List(List(1, 3), List(0, 2))
    unperform(List(1, 3), List(0, 1, 2, 3, 4)) shouldEqual List(List(1, 3))
    unperform(List(0, 2), List(0, 1, 2, 3, 4)) shouldEqual List(List(0, 2))
    unperform(List(0, 2), List(0, 1, 2, 3, 4, 0, 1)) shouldEqual List(List(0, 2, 1)) // Addition at the end
    unperform(List(0, 2), List(0, 1, 2, 0, 1, 3, 4)) shouldEqual List(List(0, 1, 2)) // Addition in the middle
    unperform(List(0, 2), List(0, 1, 0, 1, 2, 3, 4)) shouldEqual List(List(1, 0, 2)) // Addition at the beg.
    unperform(List(0, 2), List(3, 4)) shouldEqual List(List(2)) // Deletion of beginning
    unperform(List(0, 2), List(0, 1, 2)) shouldEqual List(List(0)) // Deletion of end
    unperform(List(2), List(2, 3, 4)) shouldEqual List(List(3)) // Change
    unperform(List(0, 1, 2), List(0, 1, 2, 0, 1, 2, 3, 4)) shouldEqual List(List(0, 1, 3)) // Change
    unperform(List(1, 3), List(0, 1, 0, 1, 2, 3, 4)) shouldEqual List(List(1, 1, 3)) // Addition at beg.
  }
  test("Reverse flatmap - even") {
    import d.unperform
    // Keep elements producing empty lists
    unperform(List(1, 2, 3, 4, 5), List(1, 2)) shouldEqual List(List(1, 2, 3, 4, 5))
    unperform(List(1, 2, 3, 4, 5), List(1, 3, 2)) shouldEqual List(List(1, 2, 3, 6, 4, 5))
    unperform(List(1, 2, 3, 6, 4, 5), List(1, 2)) shouldEqual List(List(1, 2, 3, 4, 5))
  }
}