import org.scalatest._

class StringReverseTest extends FunSuite with Matchers {
  import StringReverse._
  def f = append(append("Hello", " "), "world")
  def fRev(out: String): List[(String, String, String)] = appendRev("Hello ", "world", out).flatMap(leftRight => 
    appendRev("Hello", " ", leftRight._1).map(lr => (lr._1, lr._2, leftRight._2))
  )
  test("Hello world decomposition") {
    fRev("Hello world") should equal(List(("Hello", " ", "world")))
    fRev("Hello Buddy") should equal(List(("Hello", " ", "Buddy")))
    fRev("Hello big world") should equal(List(("Hello"," ","big world"), ("Hello"," big ","world"), ("Hello big"," ","world")))
    fRev("Hello a-world") should equal(List(("Hello"," ","a-world"), ("Hello"," a-","world")))
    fRev("Hello-a world") should equal(List(("Hello-a"," ","world"), ("Hello","-a ","world")))
    fRev("Hello  world") should equal(List(("Hello","  ","world"), ("Hello "," ","world"), ("Hello"," "," world")))
    fRev("Hi world") should equal(List(("Hi"," ","world")))
    fRev("Hi Buddy") should equal(List())
  }
}

class StringFormatReverseTest extends FunSuite with Matchers {
  import StringFormatReverse._
  test("Formatting reverse decomposition") {
    formatRev("%s %s %d", List("Hello", "world", 42), "Hello buddy 42") shouldEqual List(("%s %s %d", List("Hello", "buddy", 42)))
    formatRev("%s,%s %s!", List("Hello", "obscure", "world"), "Hello, obscure world!") should contain (("%s, %s %s!", List("Hello", "obscure", "world")))
    formatRev("%s,%s %s!", List("Hello", "obscure", "world"), "Hello,clear world!") should contain (("%s,%s %s!", List("Hello", "clear", "world")))
    formatRev("%s,%s %s!", List("Hello", "obscure", "world"), "Good bye,awesome friend!") should contain (("%s,%s %s!", List("Good bye", "awesome", "friend")))
    formatRev("%s$2,%s$3 %s$1!", List("world", "Hello", "obscure"), "Hello,clear world!") should contain (("%s$2,%s$3 %s$1!", List("world", "Hello", "clear")))
/*    
    fRev("Hello Buddy") should equal(List(("Hello", " ", "Buddy")))
    fRev("Hello big world") should equal(List(("Hello"," ","big world"), ("Hello"," big ","world"), ("Hello big"," ","world")))
    fRev("Hello a-world") should equal(List(("Hello"," ","a-world"), ("Hello"," a-","world")))
    fRev("Hello-a world") should equal(List(("Hello-a"," ","world"), ("Hello","-a ","world")))
    fRev("Hello  world") should equal(List(("Hello","  ","world"), ("Hello "," ","world"), ("Hello"," "," world")))
    fRev("Hi world") should equal(List(("Hi"," ","world")))
    fRev("Hi Buddy") should equal(List())*/
  }
}


class IntReverseTest extends FunSuite with Matchers {
  import IntReverse._

  def fRev(s: Int) = addRev(5, 1, s).flatMap(lr =>
    addRev(2, 3, lr._1).map(lr2 => (lr2._1, lr2._2, lr._2))
  )
  test("(2+3)+1 = 6, 5, 4, 7 repair") {
    fRev(6) should equal(List((2,3,1)))
    fRev(5) should equal(List((2,3,0), (2,2,1), (1,3,1)))
    fRev(4) should equal(List((2,3,-1), (2,1,1), (0,3,1)))
    fRev(7) should equal(List((2,3,2), (2,4,1), (3,3,1)))
  }
}

class IntValReverseTest extends FunSuite with Matchers {
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

class ListSplitTest extends FunSuite with Matchers {
  import ListSplit._
  val f = (x: Int) => x % 2 == 0
  test("Testing split reverse") {
    splitRev(List(3, 5), f, (List(3, 5), List(4))) shouldEqual List(List(4, 3, 5), List(3, 4, 5), List(3, 5, 4))
    splitRev(List(3, 4, 5), f, (List(3, 5), List())) shouldEqual List(List(3, 5))
    splitRev(List(1, 2, 3, 4, 5), f, (List(1, 3, 5), List(2, 6, 4))) shouldEqual List(List(1, 2, 6, 3, 4, 5), List(1, 2, 3, 6, 4, 5))
  }
}

class TypeSplitTest extends FunSuite with Matchers {
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

class ComposeTest extends FunSuite with Matchers {
  import Compose._
  val f = (x: Int) => x - (x % 2)
  val g = (x: Int) => x - (x % 3)
  
  val fRev = (x: Int) => if(x % 2 == 0) List(x, x+1) else Nil
  val gRev = (x: Int) => if(x % 3 == 0) List(x, x+1, x+2) else Nil

  test("Reverse composing of functions") {
    val test1 = composeRev(f, g, fRev, gRev)(0) shouldEqual List(0, 1, 2, 3)
    val test2 = composeRev(f, g, fRev, gRev)(3) shouldEqual List(4, 5)
    val test3 = composeRev(f, g, fRev, gRev)(6) shouldEqual List(6, 7, 8, 9)
  }
}

class FlattenTest extends FunSuite with Matchers {
  import Flatten._
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

class MapReverseTest extends FunSuite with Matchers {
  import MapReverse._

  val f = (x: Int) => x - (x%2)
  val fRev = (x: Int) => if(x % 2 == 0) List(x, x+1) else Nil
  test("Reversing map") {
    mapRev(List(1, 2, 3, 4, 5), f, fRev, List(0, 2, 2, 4, 4)) shouldEqual
    List(List(1, 2, 3, 4, 5))
    mapRev(List(1, 2, 3, 4, 5), f, fRev, List(0, 4, 2, 4, 4)) shouldEqual
    List(List(1, 4, 3, 4, 5), List(1, 5, 3, 4, 5))
    mapRev(List(1, 2, 3, 4, 5), f, fRev, List(0, 2, 4, 4)) should contain
    (List(1, 2, 4, 5)) //'
    mapRev(List(1, 2, 3, 4, 5), f, fRev, List(0, 2, 2, 2, 4, 4)) shouldEqual
    List(List(1, 2, 3, 2, 4, 5), List(1, 2, 3, 3, 4, 5))
  }
}

class FilterReverseTest extends FunSuite with Matchers {
  import FilterReverse._

  val isEven = (x: Int) => x % 2 == 0
  
  test("Filter reverse") {
    filterRev(List(1, 2, 3, 4, 8, 5), isEven, List(2, 4, 8)) shouldEqual
    List(List(1, 2, 3, 4, 8, 5))
    filterRev(List(1, 2, 3, 4, 8, 5), isEven, List(2, 8)) shouldEqual
    List(List(1, 2, 3, 8, 5))
    filterRev(List(1, 2, 3, 4, 8, 5), isEven, List(4, 8)) shouldEqual
    List(List(1, 3, 4, 8, 5))
    filterRev(List(1, 2, 3, 4, 8, 5), isEven, List(2, 4, 6, 8)) shouldEqual
    List(List(1, 2, 3, 4, 6, 8, 5))
    filterRev(List(1, 2, 3, 4, 8, 5), isEven, List(2, 6, 4, 8)) shouldEqual
    List(List(1, 2, 3, 6, 4, 8, 5))
  }
}


// Combines map and flatten directly.
class FlatMapTest extends FunSuite with Matchers {
  import FlatMap._
  
  val f = (x: Int) => if(x % 4 == 0) List(x, x+1, x+2) else if(x % 4 == 2) List(x+1, x+2) else if(x % 4 == 1) List(x-1, x) else List(x-1, x, x+1)
  val fRev = (lx: List[Int]) => if(lx.length == 3 && lx(1) == lx(0) + 1 && lx(2) == lx(1) + 1) {
    if(lx(0) % 4 == 0) List(lx(0))
    else if(lx(0) % 4 == 2) List(lx(1))
    else Nil
  } else if(lx.length == 2 && lx(1) == lx(0) + 1) {
    if(lx(0) % 4 == 3) List(lx(0)-1)
    else if(lx(0) % 4 == 0) List(lx(1))
    else Nil
  } else Nil
  
  // f(0) ++ f(2) == f(1) ++ f(3)
  // f(0) == [0, 1, 2]
  // f(1) == [0, 1]
  // f(2) == [3, 4]
  // f(3) == [2, 3, 4]
  
  val fEven = (x: Int) => if(x%2 == 0) List(x/2) else Nil
  val fEvenRev = (x: List[Int]) => if(x.length == 1) List(x(0)*2) else Nil
    
  test("Reverse flatmap") {
    flatMapRev(Nil, f, fRev, List(0, 1, 2, 3, 4)) shouldEqual List(List(1, 3), List(0, 2))
    flatMapRev(List(1, 3), f, fRev, List(0, 1, 2, 3, 4)) shouldEqual List(List(1, 3))
    flatMapRev(List(0, 2), f, fRev, List(0, 1, 2, 3, 4)) shouldEqual List(List(0, 2))
    flatMapRev(List(0, 2), f, fRev, List(0, 1, 2, 3, 4, 0, 1)) shouldEqual List(List(0, 2, 1)) // Addition at the end
    flatMapRev(List(0, 2), f, fRev, List(0, 1, 2, 0, 1, 3, 4)) shouldEqual List(List(0, 1, 2)) // Addition in the middle
    flatMapRev(List(0, 2), f, fRev, List(0, 1, 0, 1, 2, 3, 4)) shouldEqual List(List(1, 0, 2)) // Addition at the beg.
    flatMapRev(List(0, 2), f, fRev, List(3, 4)) shouldEqual List(List(2)) // Deletion of beginning
    flatMapRev(List(0, 2), f, fRev, List(0, 1, 2)) shouldEqual List(List(0)) // Deletion of end
    flatMapRev(List(2), f, fRev, List(2, 3, 4)) shouldEqual List(List(3)) // Change
    flatMapRev(List(0, 1, 2), f, fRev, List(0, 1, 2, 0, 1, 2, 3, 4)) shouldEqual List(List(0, 1, 3)) // Change
    flatMapRev(List(1, 3), f, fRev, List(0, 1, 0, 1, 2, 3, 4)) shouldEqual List(List(1, 1, 3)) // Addition at beg.
    
    // Keep elements producing empty lists
    flatMapRev(List(1, 2, 3, 4, 5), fEven, fEvenRev, List(1, 2)) shouldEqual List(List(1, 2, 3, 4, 5))
    flatMapRev(List(1, 2, 3, 4, 5), fEven, fEvenRev, List(1, 3, 2)) shouldEqual List(List(1, 2, 3, 6, 4, 5))
    flatMapRev(List(1, 2, 3, 6, 4, 5), fEven, fEvenRev, List(1, 2)) shouldEqual List(List(1, 2, 3, 4, 5))
  }
}