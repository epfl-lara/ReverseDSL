import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import shapeless.HList

/*
A Ground type is either a primitive type or a case class type.

RevTyping[(A1, …, An)] = (RevTyping[A1], …, RevTyping[An]) for A1, … An non-Ground.

If A is a tuple of types, let it decompose M the Ground subset of A, and 
F is the pure function subset of A.
RevTyping[A => B]  =   M => F => RevTyping[F] => Iterable[M]
In particular, if A is itself a Ground type
RevTyping[A => B]  = A => B => Iterable[A]

For f a symbol of type F, let f_$rev : RevTyping[F] if it exists

Rewriting rules:

Let {{PROGRAM}} the result of executing PROGRAM
Let’s define [[PROGRAM]](output) to be a "minimal" modification of PROGRAM producing output.
If {{PROGRAM}} = output, [[PROGRAM]](output) = PROGRAM

[[Apply(f,g)]](f_output) =
{{f_$rev(g, f_output)}}.flatMap{ input =>
  val programs = [[g]](input)
  programs.map(program => Apply(f, program))
}
If some of the g’s are high-level functions, they must be named, have a

For n≥ 2
[[(InputProgram1, … InputProgramn)]](output1, … outputn) =
[[InputProgram1]](output1).flatMap{ program =>
  [[(InputProgram2, …InputProgramn)]](output2,....outputn).map{
    case program2 =>
       TupleApply(program, program2)
  }
 }

Actually, we should produce not just a list of possible outputs.
We should produce a list index-changed new-value of possible argument modification, if only one argument is modified.

if a had the value of 2 before, and now the result of a+3+a = 5,
a+3+a should be viewed as an single expression so that we can solve it the following way.
- Take all variables and try to modify their value.
* Take all constants and try to modify their value.

If there is an assignment a = X, we try to revert the program that produced X and get a lot of possible assignments.

*/
object Common {
  def updateArgs[A <: HList](in1: A, argsUpdate: List[(Int, Any)]): A = {
    ((in1 /: argsUpdate) {
      case (a, (i, e)) => HList.unsafeUpdateAt(a, i, e).asInstanceOf[A]
    })
  }
}

/* What should be the output of an element of reverse?
- The updated list of arguments (compile-time correct)
- A list of pairs (index, value of arg modified) (compile-time not typing)
- The updated list of arguments along with which arguments are modified (to go faster to the expressions which should be modified without comparison)
*/

trait ReverseOp {
  type Input
  type Output
  def apply(in1: Input): Output
  def unapply(in1: Input, out1: Output, out2: Output): Iterable[Input]
}

object StringReverse {
  def append(s: String, t: String) = s+t
  
  def appendRev(s: String, t: String, out: String): List[(String, String)] = {
    if(s + t == out) List((s, t)) else {//Priority given to attaching space to spaces, and non-spaces to non-spaces.
      val keepFirstIntact = (if(out.length >= s.length) List((s, out.substring(s.length))) else Nil)
      val keepSecondIntact = (if(out.length >= t.length) List((out.substring(0, out.length - t.length), t)) else Nil)
      //appendRev("Hello"," ","Hello  ")  = List(("Hello", "  ") ("Hello ", " "))
      (keepFirstIntact ++ keepSecondIntact).filter(res => append(res._1, res._2) == out).sortBy{ case (s, t) =>
        if(s.length > 0 && t.length > 0) {
          if(s(s.length - 1) == ' ' && t(0) == ' ') 10
          else if(s(s.length - 1) != ' ' && t(0) != ' ') 10
          else 0
        } else 5
      }
    }
  }// ensuring { ress => ress.forall(res => append(res._1, res._2) == out) }
}
/*
object StringExtractReverse {
  def substring(s: String, start: Int, end: Int) = s.substring(s, start, end)
  
  def substringRev(s: String, start: Int, end: Int, out: String) = s.substring(0, start) + out + s.substring(end)
}*/

object StringFormatReverse {
  import java.util.regex.Pattern
  def format(s: String, args: List[Any]) = {
    //println(s"Calling '$s'.format(" + args.map(x => (x, x.getClass)).mkString(",") + ")")
    s.format(args: _*)
  }
  
  var numeroted = false // If there is $1, $2 after %s, %s, etc.
  
  // Parsing !
  def formatRev(s: String, args: List[Any], out: String): List[(String, List[Any])] = {
    // Replace all %s in s by (.*) regexes, and %d in s by (\d*) regexes.
    val formatters = "%(?:(\\d+)\\$)?((?:s|d))".r
    var i = -1
    val indexes = new ArrayBuffer[Int]()
    val splitters = formatters.findAllIn(s).matchData.map{ m => 
      (m.start, m.end, m.toString, m.subgroups(1), if(m.subgroups(0) == null) {i += 1; indexes += i; i} else { val k = m.subgroups(0).toInt - 1; indexes += k; k})
    }.toList
    val argsLength = args.length
    val substrings = ((ListBuffer[(Int, Int, String)](), 0) /: (splitters :+ ((s.length, s.length, "", "", "")))) {
      case ((lb, prevIndex), (startIndex, endIndex, _, _, _)) => (lb += ((prevIndex, startIndex, s.substring(prevIndex, startIndex))), endIndex)
    }._1.toList
    // What if indexes is not reversible? For example, indexes = [1, 1]
    //val reverseIndexes = new Array[Int](indexes.length)
    /*i = 0
    while (i < indexes.length) {
      reverseIndexes(indexes(i)) = i
      i+=1
    }
    def reverse(permutation: Array[Int], l: List[Any]): List[Any] = {
      val input = l.toArray
      (0 until input.length).toList.map(i => input(permutation(i)))
    }*/
    
    // given the elements, put them in the right order. Provides alternatives.
    def reverse(indexes: IndexedSeq[Int], l: List[Any]): List[List[Any]] = {
      //print(s"indexes : $indexes, l: $l, result = ")
      // indexes = [1, 1] and l = List(a, b) => List(List(a), List(b))
      // indexes = [1, 2] and l = List(a, b) =>  List(List(a, b))
      // indexes = [2, 3, 1] and l = List(b, c, a) =>  List(List(a, b, c))
      // indexes = [1, 2, 1] and l = List(a, b, c) =>  List(List(a, b), List(c, b))
      val zipped = indexes.zip(l).groupBy(_._1).mapValues(v => v.map(_._2))
      // zipped {1 -> List(a, b)} => List(List(a), List(b))
      // zipped {1 -> List(a), 2 -> List(b)} =>  List(List(a, b))
      // zipped {2 -> List(b), 3 -> List(c), 1 -> List(a)} =>  List(List(a, b, c))
      // zipped {1 -> List(a, c), 2 -> List(b)} =>  List(List(a, b), List(c, b))
      //val res = 
      (List(List[Any]()) /: (argsLength to 1 by -1)) {
        case (lb, i) =>
          val maps = zipped.getOrElse(i-1, List(args(i-1)))
          maps.flatMap(pos => lb.map(pos::_)).toList.distinct
      }
      //println(res)
      //res
    }
    
    // Replace all splitters by regular expressions to pattern match against anything.
    val ifargsmodifiedRegex = Pattern.quote(substrings.head._3) + splitters.map{ x => x._4 match {
      case "s" => "(.*)"
      case "d" => "(\\d*)"
    }
    }.zip(substrings.tail.map(x => Pattern.quote(x._3))).map(x => x._1 + x._2).mkString
    
    val ifargsmodified = ifargsmodifiedRegex.r.unapplySeq(out) match { // Maybe it's an argument which has been formatted.
      case Some(args2) => 
        //println("splitters:" + splitters)
        // TODO: Reorder out for comparison.
        var res = reverse(indexes, args2.zip(splitters).map{ arg_s => 
          arg_s._2._4 match {
            case "s" => arg_s._1
            case "d" => arg_s._1.toInt
          }
        })
        //println("Classes:" + res.map(l => l.map(_.getClass).mkString(",")))
        val expected = format(s, args)
        if (res.length > 1) {
          res = res.filter(otherargs => format(s, otherargs) != expected)
        }
        res.map((s, _))
      case None => Nil
    }
    val regexschange = args.map(x => Pattern.quote(x.toString)).mkString("(.*)", "(.*)", "(.*)")
    val ifsmodified =  regexschange.r.unapplySeq(out) match {
      case Some(sSplitted) => List((sSplitted.mkString("%s"), args))
      case None => Nil
    }
    ifsmodified ++ ifargsmodified
  }
}

object IntReverse {
  def add(s: Int, t: Int) = s+t
  
  def addRev(s: Int, t: Int, out: Int): List[(Int, Int)] = {
    if(s + t == out) List((s, t)) else
    List((s, out-s),  (out-t, t))
  }// ensuring { ress => ress.forall(res => add(res._1, res._2) == out) }
}

object IntValReverse {
  def add(s: Int, t: Int) = s+t
  
  def addRev(s: Int, t: Int, out: Int) = ((i: Int) => (i, out-i))
}

object ListSplit {
  def allInterleavings[A](l1: List[A], l2: List[A]): List[List[A]] = {
    if(l1.isEmpty) List(l2)
    else if(l2.isEmpty) List(l1)
    else allInterleavings(l1.tail, l2).map(l1.head :: _) ++ allInterleavings(l1, l2.tail).map(l2.head :: _)
  }
  
  def split[A](l: List[A], p: A => Boolean): (List[A], List[A]) = l match {
    case Nil => (Nil, Nil)
    case a::b => val (lfalse, ltrue) = split(b, p)
     if(p(a)) (lfalse, a::ltrue) else (a::lfalse, ltrue)
  }
  
  // Ensures that every created list has out._1.size + out._2.size
  def splitRev[A](l: List[A], p: A => Boolean, out: (List[A], List[A])):List[List[A]] = {
    out match {
      case (Nil, l2) => List(l2)
      case (l1, Nil) => List(l1)
      case (l1@ (a::b), l2 @ (c::d)) => 
        if(p(a)) Nil
        else if(!p(c)) Nil
        else if(l.isEmpty) allInterleavings(l1, l2)
        else if(!l.exists(_ == c)) // c has been added.
          splitRev(l, p, (a::b, d)).map(c::_) ++ (if(l.head == a) splitRev(l.tail, p, (b, c::d)).map(a::_) else Nil)
        else if(!l.exists(_ == a)) // a has been added.
          splitRev(l, p,(b, c::d)).map(a::_) ++ (if(l.head == c) splitRev(l.tail, p, (a::b, d)).map(c::_) else Nil)
        else if(!p(l.head) && !l1.exists(_ == l.head)) // l.head has been deleted and was in the first.
          splitRev(l.tail, p, (l1, l2))
        else if(p(l.head) && !l2.exists(_ == l.head)) // l.head has been deleted and was in the second.
          splitRev(l.tail, p, (l1, l2))
        else if(!p(l.head) && a == l.head) 
          splitRev(l.tail, p, (b, l2)).map(a::_)
        else if(p(l.head) && c == l.head)
          splitRev(l.tail, p, (l1, d)).map(c::_)
        else /*if(l.head != a && l.head != c)*/ { // l.head is no longer there.
          splitRev(l.tail, p, (l1, l2))
        }
    }
  }
}

object TypeSplit {
  abstract class Tree
  case class WebElement(tag: String, children: List[WebElement] = Nil, attributes: List[WebAttribute] = Nil, styles: List[WebStyle] = Nil) extends Tree
  case class WebAttribute(name: String, value: String) extends Tree
  case class WebStyle(name: String, value: String) extends Tree
  import ListSplit.allInterleavings
  
  def split(l: List[Tree]): (List[WebElement], List[WebAttribute], List[WebStyle]) = l match {
    case Nil => (Nil, Nil, Nil)
    case a::b => val (l1, l2, l3) = split(b)
     a match {
       case w: WebElement => (w::l1, l2, l3)
       case w: WebAttribute => (l1, w::l2, l3)
       case w: WebStyle => (l1, l2, w::l3)
     }
  }

  // Ensures that every created list has out._1.size + out._2.size
  def splitRev(l: List[Tree], out: (List[WebElement], List[WebAttribute], List[WebStyle])):List[List[Tree]] = {
    out match {
      case (l1, l2, l3) =>
        l match {
          case Nil => allInterleavings(l1, l2).flatMap(l1l2 => allInterleavings(l1l2, l3))
          case lh::lt => 
            lh match {
              case lh: WebElement =>
                l1 match {
                  case Nil => // An element was deleted.
                    splitRev(lt, (l1, l2, l3))
                  case l1h::l1t =>
                    if (lh == l1h) {
                      splitRev(lt, (l1t, l2, l3)).map(lh::_)
                    } else if(!l.exists(_ == l1h)) { // l1h was added
                      splitRev(l, (l1t, l2, l3)).map(l1h::_)
                    } else { // It exists later, so lh was removed.
                      splitRev(lt, (l1, l2, l3))
                    }
                }
              case lh: WebAttribute =>
                l2 match {
                  case Nil => // An element was deleted.
                    splitRev(lt, (l1, l2, l3))
                  case l2h::l2t =>
                    if (lh == l2h) {
                      splitRev(lt, (l1, l2t, l3)).map(lh::_)
                    } else if(!l.exists(_ == l2h)) { // l2h was added
                      splitRev(l, (l1, l2t, l3)).map(l2h::_)
                    } else { // It exists later, so lh was removed.
                      splitRev(lt, (l1, l2, l3))
                    }
                }
              case lh: WebStyle =>
                l3 match {
                  case Nil => // An element was deleted.
                    splitRev(lt, (l1, l2, l3))
                  case l3h::l3t =>
                    if (lh == l3h) {
                      splitRev(lt, (l1, l2, l3t)).map(lh::_)
                    } else if(!l.exists(_ == l3h)) { // l3h was added
                      splitRev(l, (l1, l2, l3t)).map(l3h::_)
                    } else { // It exists later, so lh was removed.
                      splitRev(lt, (l1, l2, l3))
                    }
                }
            }
        }
    }
  }
}

object WebElementAddition {
  import TypeSplit._
  type Input = (WebElement, List[WebElement], List[WebAttribute], List[WebStyle])
  type Output = WebElement
  
  def apply(elem: WebElement, children: List[WebElement], attributes: List[WebAttribute], styles: List[WebStyle]): WebElement = {
    WebElement(elem.tag, elem.children ++ children, elem.attributes ++ attributes, elem.styles ++ styles)
  }
  
  def applyRev(in: Input, out: Output): List[Input] = {
    val elem = in._1
    val children = in._2
    val attributes = in._3
    val styles = in._4
    // If the original element could have been not modified
    val ifOriginalElemNotModified : List[Input] = if(
        out.children.take(elem.children.length) == elem.children &&
        out.attributes.take(elem.attributes.length) == elem.attributes &&
        out.styles.take(elem.styles.length) == elem.styles) {
      List((elem,
            out.children.drop(elem.children.length),
            out.attributes.drop(elem.attributes.length),
            out.styles.drop(elem.styles.length))
      )
    } else Nil
    val ifAdditionsNotModified : List[Input] = if(
      out.children.takeRight(children.length) == children &&
      out.attributes.takeRight(attributes.length) == attributes &&
      out.styles.takeRight(styles.length) == styles) {
      List((WebElement(elem.tag,
        out.children.dropRight(children.length),
        out.attributes.dropRight(attributes.length),
        out.styles.dropRight(styles.length)),
           children,
           attributes,
           styles
        ))
    } else Nil
    (ifOriginalElemNotModified ++ ifAdditionsNotModified).distinct
  }
}
/*
object WebElementComposition {
  import TypeSplit._
  type Input = (WebElement, List[Tree])
  type Output = WebElement
  
  def apply(elem: WebElement, subs: List[Tree]): WebElement = {
    val (children, attrs, styles) = split(subs)
    WebElement(elem.tag, elem.children ++ children, elem.attributes ++ attrs, elem.styles ++ styles)
  }
  
  def applyRev(in: Input, out: Output): List[Input] = {
    val elem = in._1
    val subs = in._2
    val expected_output = apply(elem, subs)
    splitRev((out.children, out.attributes, out.styles))
  }
  
  import ListSplit.allInterleavings
}*/

object Compose {
  def compose[A, B, C](f: A => B, g: B => C): A => C = (x: A) => g(f(x))
  
  def composeRev[A, B, C](f: A => B, g: B => C, fRev: B => List[A], gRev: C => List[B]): C => List[A] = { (out: C) =>
    gRev(out).flatMap(b => fRev(b)).distinct
  }
}

object Flatten {
  def flatten[A](l: List[List[A]]): List[A] = l.flatten
  
  def flattenRev[A](l: List[List[A]], out: List[A]): List[List[List[A]]] = {
    l match {
      case Nil => List(List(out))
      case a::Nil => List(List(out))
      case a::(q@(b::p)) => if(out.take(a.length) == a) {
        flattenRev(q, out.drop(a.length)).map(a::_)
      } else { // Something happened, a sequence inserted or deleted, or some elements changed.
        if(out == a.take(out.length)) { // it was a prefix.
          List(List(out))
        } else {
          val aZipOut = a.zip(out) // of length a.length
          val sameStart = aZipOut.takeWhile(x => x._1 == x._2) // of length < a.length
          val missedSeq = a.drop(sameStart.length)
          val restartIndex = out.indexOfSlice(missedSeq)
          if(restartIndex != -1) { // There has been an addition in the output, but we can recover.
            val t = restartIndex + missedSeq.length
            flattenRev(q, out.drop(t)).map(out.take(t)::_)
          } else { // Maybe there has been a deletion in the output.
            for{sizeOfDeletion <- (1 to (a.length - sameStart.length)).toList
                lookingFor = a.drop(sameStart.length + sizeOfDeletion)
                indexOfLookingFor = (if(lookingFor.length > 0) out.indexOfSlice(lookingFor, sameStart.length)
                                     else sameStart.length)
                if indexOfLookingFor != -1
                t = indexOfLookingFor + lookingFor.length
                y <- flattenRev(q, out.drop(t))
            } yield (out.take(t)::y)
          }
//          ini =a[1 2 3 4 9] [5 6] [] [7] // restartIndex != -1
//          out = [1 2 3 2 4 9 5 6 7]

//          ini =a[1 2 3 2 4 8] [5 6] [] [7] // restartIndex == -1
//          out = [1 2 3 5 6 7]
        }
      }
    }
  } // ensuring res => res.forall(sol => sol.flatten == out && lehvenstein(l, sol) == lehvenstein(out, sol.flatten))
  
}

object MapReverse {
  def map[A, B](l: List[A], f: A => B): List[B] = l map f
  
  def combinatorialMap[A, B](l: List[A], f: A => List[B]): List[List[B]] = {
    l match {
      case Nil => List(Nil)
      case a::b => f(a).flatMap(fb => combinatorialMap(b, f).map(fb::_))
    }
  }
  
  def mapRev[A, B](l: List[A], f: A => B, fRev: B => List[A], out: List[B]): List[List[A]] = {
    l match {
      case Nil => 
        out match {
          case Nil => List(Nil)
          /*case outhd::Nil => fRev(outhd).map(List(_))*/
          case outhd::outtail => 
            val revOutHd = fRev(outhd)
            for{ sol <- mapRev(l, f, fRev, outtail)
                 other_a <- revOutHd } yield {
              other_a :: sol
            }
        }
      case hd::tl =>
       out match {
         case Nil => List(Nil)
         /*case outhd::Nil =>
           val revOutHd = fRev(outhd)
           val p = revOutHd.filter(_ == hd)
           if(p.isEmpty) {
             revOutHd.map(List(_))
           } else {
             p.map(List(_))
           }*/
         case outhd::outtail =>
           val revOutHd = fRev(outhd)
           val p = revOutHd.filter(_ == hd)
           if(p.isEmpty) { // Looking for a deleted element maybe ?
             val expectedOut = l map f
             val k = expectedOut.indexOfSlice(out)
             if(k > 0) { // There has been a deletion, but we are able to find the remaining elements.
               mapRev(l.drop(k), f, fRev, out)
             } else {
               val k2 = out.indexOfSlice(expectedOut)
               if(k2 > 0) { // Some elements were added at some point.
                 val tailSolutions = mapRev(l, f, fRev, out.drop(k2))
                 // Now for each of out.take(k2), we take all possible inverses.
                 combinatorialMap(out.take(k2), fRev).flatMap(l => tailSolutions.map(l ++ _))
               } else {
                 revOutHd.flatMap(s => mapRev(tl, f, fRev, outtail).map(s::_))
               }
             }
           } else {
             p.flatMap(s => mapRev(tl, f, fRev, outtail).map(s::_))
           }
       }
    }
  }// ensuring res => res.forall(sol => map(sol, f) == out && lehvenstein(l, sol) == lehvenstein(out, map(sol, f)))
}

object FilterReverse {
  def filter[A](l: List[A], f: A => Boolean): List[A] = l filter f
  
  def filterRev[A](l: List[A], f: A => Boolean, out: List[A]): List[List[A]] = {
    if(l.filter(f) == out) List(l) else
    (l match {
      case Nil => 
        if(out forall f) List(out) else Nil
      case hd::tl =>
        if(!f(hd)) {
          /*for{sol <- filterRev(tl, f, out)
            c = sol.indexWhere((x: A) => !f(x))
            i <- 0 to (if(c == -1) sol.length else c)
          } yield {
            sol.take(i) ++ (hd ::sol.drop(i))
          }*/ // Too much possibilities
          filterRev(tl, f, out).map(hd::_)
        } else { // hd has to be kept
          out match {
            case Nil => List(tl.filter(x => !f(x)))
            case outhd::outtl =>
              if(outhd == hd) {
                filterRev(tl, f, outtl).map(outhd::_)
              } else { // Find if elements have been deleted.
                // hd != outhd, either we can find it later or it has been deleted.
                val expectedFiltered_l = l.filter(f)
                val k = out.indexOfSlice(expectedFiltered_l)
                if(k > 0) { // There has been some additions in out, we add them directly.
                  filterRev(l, f, out.drop(k)).map(out.take(k)++_)
                } else {
                  // Maybe some elements have been deleted.
                  filterRev(tl, f, out)
                }
              }
          }
        }
    })
  }// ensuring res => res.forall(sol => filter(sol, f) == out && lehvenstein(l, sol) == lehvenstein(out, filter(sol, f))
}

object FlatMap {
  def flatMap[A, B](l: List[A], f: A => List[B]): List[B] = l.flatMap(f)

  def flatMapRev[A, B](l: List[A], f: A => List[B], fRev: List[B] => List[A], out: List[B]): List[List[A]] = {
    l match {
      case Nil =>
        out match {
          case Nil => List(Nil)
          case _ =>
            for{i <- (1 to out.length).toList
                out_take_i = out.take(i)
                a <- fRev(out_take_i)
                sol <- flatMapRev(l, f, fRev, out.drop(i))} yield {
              a::sol
            }
        }
      case ha::tail =>
        val expectedout = f(ha)
        if(expectedout.length == 0) {
          flatMapRev(tail, f, fRev, out).map(ha::_)
        } else if(out == expectedout) {
          flatMapRev(tail, f, fRev, Nil).map(ha::_)
        } else if(out.take(expectedout.length) == expectedout) { // There has been an addition at the end
          val t = flatMapRev(tail, f, fRev, out.drop(expectedout.length)).map(ha::_)
          if(t.isEmpty) { // Fallback: We completely remove the hint
            flatMapRev(Nil, f, fRev, out)
          } else t
        } else {
          val k = out.indexOfSlice(expectedout)
          if(k > 0) {
            val frevouttakek = fRev(out.take(k))
            val t = for{ sol <- flatMapRev(tail, f, fRev, out.drop(k + expectedout.length))
                 a <- frevouttakek
              } yield {
                 a::ha::sol
            }
            if(t.isEmpty) {
              flatMapRev(Nil, f, fRev, out)
            } else t
          } else {
            flatMapRev(tail, f, fRev, out)
          }
        }
    }
  }
}
