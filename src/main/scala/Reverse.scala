import ImplicitTuples.tuple2

import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import shapeless.HList
import Implicits._
import inox._
import inox.trees._
import inox.trees.dsl._
import Constrainable._

/** Lense class.
  * Should provide the method get and put.
  */
abstract class ~~>[A: Constrainable, B: Constrainable] {
  type Input = A
  type Output = B
  def get(in: A): B
  def put(out2: Variable, inId: Variable, in1: Option[A]): Constraint[A]

  lazy val constrainableInput: Constrainable[A] = implicitly[Constrainable[A]]
  lazy val constrainableOutput: Constrainable[B] = implicitly[Constrainable[B]]

  // Basic implementation provided in ~~=>.put
  def put(out2: B, in1: Option[A]): Iterable[A]

  final def put(out2: B, in1: A): Iterable[A] = put(out2, Some(in1))
  final def put(out2: B): Iterable[A] = put(out2, None)
  def andThen[C: Constrainable](f: B ~~> C) = Compose(f, this)
}

/** Particular case of ~~=> Implementing the direct put method as immediate constraint solving. */
abstract class ~~=>[A: Constrainable, B: Constrainable]  extends (A ~~> B) {
  val name: String
  def put(out: Output, st: Option[Input]): Iterable[Input] = report(s"$name.put($out, $st) = %s"){
    val outId = variable[Output]("out")
    val inId = variable[Input]("in")
    val constraint = put(outId, inId, st)
    constraint(outId -> out).toStream(inId)
  }
}

/** A way to provide a manual reverse of the transformation */
trait ManualReverse[A, B] extends (A ~~> B) {

  def putManual(out2: B, in1: Option[A]): Iterable[A]
}

object Common {
  val maybe : Identifier = FreshIdentifier("maybe")
}

// Definition of multiple lenses

/** String concatenation lens */
object StringAppendReverse extends ((String, String) ~~=> String) {
  import ImplicitTuples._

  def get(in: (String, String)): String = in._1 + in._2

  val name = "StringAppend"

  override def put(o: Variable, i: Variable, in1: Option[(String, String)]): Constraint[(String, String)] = {
    val expr = in1 match {
      case None =>
        StringConcat(i.getField(_1), i.getField(_2)) === o
      case Some((a, b)) =>
          StringConcat(i.getField(_1), E(b)) === o && E(Common.maybe)(i.getField(_2) === E(b)) ||
          StringConcat(E(a), i.getField(_2)) === o && E(Common.maybe)(i.getField(_1) === E(a)) ||
          StringConcat(i.getField(_1), i.getField(_2)) === o
    }
    Constraint[(String, String)](expr)
  }
}

/** Integer addition lens */
object IntPlusReverse extends ((Int, Int) ~~=> Int) {
  import ImplicitTuples._
  def get(st: (Int, Int)) = st._1 + st._2
  val name = "IntPlus"

  def put(o: Variable, i: Variable, in1: Option[(Int, Int)]) = {
    val expr = in1 match {
      case None =>
        i.getField(_1) + i.getField(_2) === o
      case Some((a, b)) =>
        (i.getField(_1) + i.getField(_2) === o) && E(Common.maybe)(i.getField(_2) === E(b)) && E(Common.maybe)(i.getField(_1) === E(a))
    }
    Constraint[(Int, Int)](expr)
  }
}

/*
object StringExtractReverse {
  def substring(s: String, start: Int, end: Int) = s.substring(s, start, end)
  
  def substringRev(s: String, start: Int, end: Int, out: String) = s.substring(0, start) + out + s.substring(end)
}*/

object StringFormatReverse extends ((String, List[Either[String, Int]]) ~~=> String) with ManualReverse[(String, List[Either[String, Int]]), String]{
  import java.util.regex.Pattern
  def format(s: String, args: List[Either[String, Int]]) = {
    //println(s"Calling '$s'.format(" + args.map(x => (x, x.getClass)).mkString(",") + ")")
    s.format(args.map{ case Left(i) => i : Any case Right(i) => i : Any}: _*)
  }
  def get(in: Input) = format(in._1, in._2)
  val name = "StringFormat"

  def putManual(out2: Output, in: Option[Input]): Iterable[Input] =
    in match {
    case None =>
      List(("%s", List(Left(out2))))
    case Some(in) =>
      formatRev(in._1, in._2, out2)
  }

  // Parsing !
  def formatRev(s: String, args: List[Either[String, Int]], out: String): List[(String, List[Either[String, Int]])] = {
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
    
    // given the elements, put them in the right order. Provides alternatives.
    def reverse(indexes: IndexedSeq[Int], l: List[Either[String, Int]]): List[List[Either[String, Int]]] = {
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
      (List(List[Either[String, Int]]()) /: (argsLength to 1 by -1)) {
        case (lb, i) =>
          val maps: Seq[Either[String, Int]] = zipped.getOrElse(i-1, List(args(i-1)))
          maps.flatMap(pos => lb.map(pos::_)).toList.distinct
      }
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
            case "s" => Left(arg_s._1)
            case "d" => Right(arg_s._1.toInt)
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

  def put(o: Variable, i: Variable, in: Option[(String, List[Either[String, Int]])]): Constraint[(String, List[Either[String, Int]])] = {
    val format = FreshIdentifier("format")
    val expr = Equals(E(format)(i, inoxExprOf(in)), o)
    //println("Constraint inferred:" + expr)
    Constraint[(String, List[Either[String, Int]])](expr, Map(format -> this.asInstanceOf[ManualReverse[B forSome { type B },C forSome { type C }]]))
  }
}
/*
import scala.util.matching.Regex
case class RegexReplaceAllInReverse(regex: Regex, f: List[String] ~~> String) extends (String ~~> String) {
  import java.util.regex.Pattern
  def get(in: String): String = regex.replaceAllIn(in, m => f.get(m.subgroups))
  def put(out: String, in: Option[String]): Constraint[String] = {
     in match {
       case None => Nil // Maybe something better than Nil?
       case Some(in) => // Let's figure out where f did some replacement.
         val matches = regex.findAllMatchIn(in)
         
         var lastEnd = 0
         val stringMatchPairs = (for{m <- matches.toList.view
             start = m.start
             end = m.end
             str = in.substring(lastEnd, start)
         } yield {
            lastEnd = end
            (str, m)
         })
         val (strings, mm) = stringMatchPairs.toList.unzip
         val allstrings = strings :+ in.substring(lastEnd)
         // Now we are going to parse the original string using all strings to recover the new output of each f element:
         val ifReplacedContentChanged = (Pattern.quote(allstrings.head) + allstrings.tail.map{
           case s => "(.*)" + Pattern.quote(s)
         }.mkString).r
         val ifReplacedConstantChanged = ("(.*)" + mm.toList.map{
           case m => Pattern.quote(f.get(m.subgroups)) + "(.*)"
         }.mkString).r
         val replacedConstantSolutions = ifReplacedConstantChanged.unapplySeq(out) match {
           case Some(ss) => 
           List(ss.zip(mm).map{ case (a, b) => a + b.matched}.mkString + ss.last)
           case None => Nil
         }
         val replacedContentSolutions: Constraint[String] = ifReplacedContentChanged.unapplySeq(out) match {
           case Some(ss) => 
             // Need to compute the values of f now and put back the content into them.
             val unplexedResult = mm.zip(ss) map { case (m, s) =>
               val init = m.subgroups
               f.put(s, Some(init)).toStream.map{
                 (fargs: List[String]) =>
                   // Need to re-plug fargs inside the regex.
                   // For that we need to split the group.
                   val globalstart = m.start(0)
                   var lastEnd = m.start(0)
                   val externalGroups = for{i <- (1 to m.groupCount).toList.view
                       start = m.start(i)
                       end = m.end(i)
                       str = m.matched.substring(lastEnd - globalstart, start - globalstart)
                   } yield {
                     lastEnd = end
                     str
                   }
                   externalGroups.zip(fargs).map{ case (a, b) => a + b}.mkString + m.matched.substring(lastEnd - globalstart)
               }
             }
             val plexedResult = cartesianProduct(unplexedResult)
             plexedResult.map{ (contents: List[String]) =>
               allstrings.zip(contents).map{ case (a, b) => a + b}.mkString + allstrings.last
             }
           // These are the new values to pass to f.
           case None => Nil
         }
         replacedConstantSolutions ++ replacedContentSolutions
     }
  }
  
   def cartesianProduct[T](streams : Seq[Stream[T]]) : Stream[List[T]] = {
    val dimensions = streams.size
    val vectorizedStreams = streams.map(new VectorizedStream(_))

    if(dimensions == 0)
      return Stream.cons(Nil, Stream.empty)

    if(streams.exists(_.isEmpty))
      return Stream.empty

    val indices = diagCount(dimensions)

    var allReached : Boolean = false
    val bounds : Array[Option[Int]] = for (s <- streams.toArray) yield {
      if (s.hasDefiniteSize) {
        Some(s.size)
      } else {
        None
      }
    }

    indices.takeWhile(_ => !allReached).flatMap { indexList =>
      var d = 0
      var continue = true
      var is = indexList
      var ss = vectorizedStreams.toList

      if ((indexList zip bounds).forall {
          case (i, Some(b)) => i >= b
          case _ => false
        }) {
        allReached = true
      }

      var tuple : List[T] = Nil

      while(continue && d < dimensions) {
        val i = is.head
        if(bounds(d).exists(i > _)) {
          continue = false
        } else try {
          // TODO can we speed up by caching the random access into
          // the stream in an indexedSeq? After all, `i` increases
          // slowly.
          tuple = ss.head(i) :: tuple
          is = is.tail
          ss = ss.tail
          d += 1
        } catch {
          case e : IndexOutOfBoundsException =>
            bounds(d) = Some(i - 1)
            continue = false
        }
      }
      if(continue) Some(tuple.reverse) else None
    }
  }
  private def diagCount(dim : Int) : Stream[List[Int]] = diag0(dim, 0)
  private def diag0(dim : Int, nextSum : Int) : Stream[List[Int]] = summingTo(nextSum, dim).append(diag0(dim, nextSum + 1))

  private def summingTo(sum : Int, n : Int) : Stream[List[Int]] = {
    if(sum < 0) {
      Stream.empty
    } else if(n == 1) {
      Stream.cons(sum :: Nil, Stream.empty) 
    } else {
      (0 to sum).toStream.flatMap(fst => summingTo(sum - fst, n - 1).map(fst :: _))
    }
  }
  private class VectorizedStream[T](initial : Stream[T]) {
    private def mkException(i : Int) = new IndexOutOfBoundsException("Can't access VectorizedStream at : " + i)
    private def streamHeadIndex : Int = indexed.size
    private var stream  : Stream[T] = initial
    private var indexed : Vector[T] = Vector.empty

    def apply(index : Int) : T = {
      if(index < streamHeadIndex) {
        indexed(index)
      } else {
        val diff = index - streamHeadIndex // diff >= 0
        var i = 0
        while(i < diff) {
          if(stream.isEmpty) throw mkException(index)
          indexed = indexed :+ stream.head
          stream  = stream.tail
          i += 1
        }
        // The trick is *not* to read past the desired element. Leave it in the
        // stream, or it will force the *following* one...
        stream.headOption.getOrElse { throw mkException(index) }
      }
    }
  }
}


object IntReverse extends ((Int, Int) ~~> Int) {
  def add(s: Int, t: Int) = s+t
  def get(in: Input): Output = add(in._1, in._2)
  def put(out2: Output, in: Option[Input]): Constraint[Input] = in match {
    case None => List((out2, 0))
    case Some(in) => addRev(in._1, in._2, out2)
  }
  
  def addRev(s: Int, t: Int, out: Int): List[(Int, Int)] = {
    if(s + t == out) List((s, t)) else
    List((s, out-s),  (out-t, t))
  }// ensuring { ress => ress.forall(res => add(res._1, res._2) == out) }
}

object Interleavings {
  def allInterleavings[A](l1: List[A], l2: List[A]): List[List[A]] = {
    if(l1.isEmpty) List(l2)
    else if(l2.isEmpty) List(l1)
    else allInterleavings(l1.tail, l2).map(l1.head :: _) ++ allInterleavings(l1, l2.tail).map(l2.head :: _)
  }
}

class ListSplit[A](p: A => Boolean) extends (List[A] ~~> (List[A], List[A])) {
  import Interleavings._
  
  def get(in: Input): Output = split(in)
  def put(out2: Output, in: Option[Input]) = in match {
    case None => List(out2._1 ++ out2._2)
    case Some(in) => splitRev(in, out2)
  }
  
  def split(l: List[A]): (List[A], List[A]) = l match {
    case Nil => (Nil, Nil)
    case a::b => val (lfalse, ltrue) = split(b)
     if(p(a)) (lfalse, a::ltrue) else (a::lfalse, ltrue)
  }
  
  // Ensures that every created list has out._1.size + out._2.size
  def splitRev(l: List[A], out: (List[A], List[A])):List[List[A]] = {
    out match {
      case (Nil, l2) => List(l2)
      case (l1, Nil) => List(l1)
      case (l1@ (a::b), l2 @ (c::d)) => 
        if(p(a)) Nil
        else if(!p(c)) Nil
        else if(l.isEmpty) allInterleavings(l1, l2)
        else if(!l.exists(_ == c)) // c has been added.
          splitRev(l, (a::b, d)).map(c::_) ++ (if(l.head == a) splitRev(l.tail, (b, c::d)).map(a::_) else Nil)
        else if(!l.exists(_ == a)) // a has been added.
          splitRev(l, (b, c::d)).map(a::_) ++ (if(l.head == c) splitRev(l.tail, (a::b, d)).map(c::_) else Nil)
        else if(!p(l.head) && !l1.exists(_ == l.head)) // l.head has been deleted and was in the first.
          splitRev(l.tail, (l1, l2))
        else if(p(l.head) && !l2.exists(_ == l.head)) // l.head has been deleted and was in the second.
          splitRev(l.tail, (l1, l2))
        else if(!p(l.head) && a == l.head) 
          splitRev(l.tail, (b, l2)).map(a::_)
        else if(p(l.head) && c == l.head)
          splitRev(l.tail, (l1, d)).map(c::_)
        else /*if(l.head != a && l.head != c)*/ { // l.head is no longer there.
          splitRev(l.tail, (l1, l2))
        }
    }
  }
}

object WebTrees {
  var displayNiceDSL = true
  abstract class Tree extends Product with Serializable
  abstract class WebElement extends Tree
  case class TextNode(text: String) extends WebElement {
    override def toString = if(displayNiceDSL) "\"" + "\"".r.replaceAllIn("\\\\".r.replaceAllIn(text, "\\\\\\\\"), "\\\"") + "\"" else s"TextNode($text)"
  }
  object TextNode {
    def apply[A](f: (A ~~> String)): (A ~~> TextNode) = new (A ~~> TextNode) {
      def get(a: A) = TextNode(f.get(a))
      def put(t: TextNode, in: Option[A]): Constraint[A] = {
        f.put(t.text, in)
      }
    }
  }
  object Element {
    def apply[A](tag: String, f: A ~~> List[WebElement]): (A ~~> Element) = {
      new (A ~~> Element) {
        def get(a: A) = Element(tag, f.get(a))
        def put(e: Element, in: Option[A]): Constraint[A] = Implicits.report(s"Element.put($e, $in) = %s") {
          f.put(e.children, in)
        }
      }
    }
  }
  case class Element(tag: String, children: List[WebElement] = Nil, attributes: List[WebAttribute] = Nil, styles: List[WebStyle] = Nil) extends WebElement {
    override def toString = if(displayNiceDSL) "<." + tag + (if(children.nonEmpty || attributes.nonEmpty || styles.nonEmpty) (children ++ attributes ++ styles).mkString("(", ", ", ")") else "") else {
      if(styles.isEmpty) {
        if(attributes.isEmpty) {
          if(children.isEmpty) {
            s"Element($tag)"
          } else {
            s"Element($tag,$children)"
          }
        } else {
          s"Element($tag,$children,$attributes)"
        }
      } else
      s"Element($tag,$children,$attributes,$styles)"
    }
    
    def apply[A](f: (A ~~> List[Tree])): (A ~~> Element) = {
      Pair(Const(this), f) andThen WebElementComposition
    }
    def apply(l: List[Tree]): Element = WebElementComposition.get((this, l))
  }
  case class WebAttribute(name: String, value: String) extends Tree {
    override def toString = if(displayNiceDSL) "^." + name + " := " + value else super.toString
  }
  case class WebStyle(name: String, value: String) extends Tree {
    override def toString = if(displayNiceDSL) "^." + name + " := " + value else super.toString
  }
}
import WebTrees._

object TypeSplit extends (List[Tree] ~~> (List[WebElement], List[WebAttribute], List[WebStyle])) {
  import Interleavings._
  def get(in: Input): Output = split(in)
  def put(out2: Output, in1: Option[Input]): Constraint[Input] = in1 match {
    case None =>
      List(out2._1 ++ out2._2 ++ out2._3)
    case Some(in1) =>
      splitRev(in1, out2)
  }
  
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

object WebElementAddition extends ((Element, (List[WebElement], List[WebAttribute], List[WebStyle])) ~~> Element) {
  
  def get(in: Input) = apply(in._1, in._2._1, in._2._2, in._2._3)
  def put(out2: Output, in: Option[Input]) = in match {
    case None => List((out2, (Nil, Nil, Nil)))
    case Some(in) => applyRev(in, out2)
  }

  def apply(elem: Element, children: List[WebElement], attributes: List[WebAttribute], styles: List[WebStyle]): Element = {
    Element(elem.tag, elem.children ++ children, elem.attributes ++ attributes, elem.styles ++ styles)
  }
  
  def applyRev(in: Input, out: Output): List[Input] = {
    val elem = in._1
    val children = in._2._1
    val attributes = in._2._2
    val styles = in._2._3
    // If the original element could have been not modified
    val ifOriginalElemNotModified : List[Input] = if(
        out.children.take(elem.children.length) == elem.children &&
        out.attributes.take(elem.attributes.length) == elem.attributes &&
        out.styles.take(elem.styles.length) == elem.styles) {
      List((elem,
            (out.children.drop(elem.children.length),
            out.attributes.drop(elem.attributes.length),
            out.styles.drop(elem.styles.length)))
      )
    } else Nil
    val ifAdditionsNotModified : List[Input] = if(
      out.children.takeRight(children.length) == children &&
      out.attributes.takeRight(attributes.length) == attributes &&
      out.styles.takeRight(styles.length) == styles) {
      List((Element(elem.tag,
        out.children.dropRight(children.length),
        out.attributes.dropRight(attributes.length),
        out.styles.dropRight(styles.length)),
           (children,
           attributes,
           styles)
        ))
    } else Nil
    (ifOriginalElemNotModified ++ ifAdditionsNotModified).distinct
  }
}

object WebElementComposition extends ((Element, List[Tree])  ~~> Element) {
  def get(in: Input): Output = {
    WebElementAddition.get(in._1, TypeSplit.get(in._2))
  }

  def put(out2: Output, in: Option[Input]): Constraint[Input] = Implicits.report(s"WebElementComposition($in, $out2) = %s")(in match {
    case None =>
      val l = out2.children ++ out2.attributes ++ out2.styles
      for{ i <- 0 to l.length
        (lhs, rhs) = l.splitAt(i)
      } yield { (get((Element(out2.tag), lhs)), rhs)}
    case Some(in) =>
    val originalMiddle = TypeSplit.get(in._2)
    WebElementAddition.put(out2, (in._1, originalMiddle)).flatMap{ case (elem, cas) => 
      TypeSplit.put(cas, in._2).map{ s => (elem, s) }
    }
  })
}
/*
case class Compose[A, B, C](f: A => B, g: B => C, fRev: B => Constraint[A], gRev: C => Constraint[B]) extends ~~> {
  type Input = A
  type Output = C
  def get(in: Input) = g(f(in))
  
  def put(in: Input, out2: Output) = 
    gRev(out2).flatMap(b => fRev(b))
}*/

// Make sure the types agree !!*/

case class Compose[A: Constrainable, B: Constrainable, C: Constrainable](a: B ~~> C, b: A ~~> B) extends (A ~~> C) {
  def get(in: Input): Output = a.get(b.get(in).asInstanceOf[a.Input])
  def put(out2: Output, in: Option[Input]) = {
   val intermediate_out = in.map(b.get)
   a.put(out2, intermediate_out).flatMap(x => b.put(x, in))
  }

  override def put(idC: Variable, idA: Variable, in1: Option[A]): Constraint[A] = {
    val idB = variable[B]("t", true)
    val intermediate_out = in1.map(b.get) // TODO: Have it pre-computed already
    a.put(idC, idB, intermediate_out) <&&
      b.put(idB, idA, in1)
  }
}

case class PairSame[A: Constrainable, B: Constrainable, D: Constrainable](a: A ~~> B, b: A ~~> D)
    extends (A ~~=> (B, D)) {
  def get(in: Input): Output = (a.get(in), b.get(in))
  //def put(out2: Output, in: Option[Input]): Iterable[Input] = ???
  import ImplicitTuples._
  val name = "Pair"

  def put(varBD: Variable, varA: Variable, in: Option[A]): Constraint[A] = {
    val varB = variable[B]("b", true)
    val varD = variable[D]("d", true)
    a.put(varB, varA, in) &&
      b.put(varD, varA, in) &&
      varB === varBD.getField(_1) &&
      varD === varBD.getField(_2)
  }
}
/*
case class Flatten[A]() extends (List[List[A]] ~~> List[A]) {
  def get(in: Input) = flatten(in)
  def put(out2: Output, in: Option[Input]) = in match {
    case None => List(List(out2))
    case Some(in) => flattenRev(in, out2)
  }

  def allUnflattenings(out: List[A]): Stream[List[List[A]]] = {
    out match {
      case Nil => Stream(List())
      case out => 
        for{i <- Stream.from(1).take(out.length)
            outhead = out.take(i)
            outtail = out.drop(i)
            other <- allUnflattenings(outtail)
          } yield {
          outhead :: other
        }
    }
  }

  def flatten(l: List[List[A]]): List[A] = l.flatten
  
  def flattenRev(l: List[List[A]], out: List[A]): Stream[List[List[A]]] = {
    l match {
      case Nil => 
        if(out == Nil) Stream(List()) else
        allUnflattenings(out) // We should create all possible decompositions of out.
      //case a::Nil => if(a == out) List(List(out)) else allUnflattenings(out)
      case a::q => if(out.take(a.length) == a) {
        (if (out.length == a.length) {
          Stream(List(a))
        } else Stream.empty) #:::
        (flattenRev(q, out.drop(a.length)).map(a::_))
      } else { // Something happened, a sequence inserted or deleted, or some elements changed.
        if (out == a.take(out.length)) { // it was a prefix of the current list.
          Stream(List(out))
        } else {
          val expected_flatten = flatten(l)
          if (out.endsWith(expected_flatten)) {
            val missing = out.dropRight(expected_flatten.length)
            ((missing ++ a) :: q) #:: (
            for{ toTakeAlone <- Stream.from(1).take(missing.length)
                 alone = missing.take(toTakeAlone)
                 missingAttached = missing.drop(toTakeAlone)
                 alone_decomposition <- allUnflattenings(alone)
                 } yield {
              alone_decomposition ++ ((missingAttached ++ a)::q)
            })
          } else if (expected_flatten.endsWith(out)) { // Elements have been deleted.
            val flattenq = flatten(q)
            if (flattenq.endsWith(out)) {
              flattenRev(q, out)
            } else { // out is slightly longer than q and ends with flattenQ.
              val missing = out.dropRight(flattenq.length)
              assert(a.endsWith(missing))
              flattenRev(a.drop(a.length - missing.length)::q, out)
            }
          } else {
            val aZipOut = a.zip(out) // of length a.length
            val sameStart = aZipOut.takeWhile(x => x._1 == x._2) // of length < a.length
            val missedSeq = a.drop(sameStart.length)
            val restartIndex = out.indexOfSlice(missedSeq)
            if (restartIndex != -1) { // There has been an addition in the output, but we can recover.
              val t = restartIndex + missedSeq.length
              flattenRev(q, out.drop(t)).map(out.take(t)::_)
            } else { // Maybe there has been a deletion in the output.
              for{sizeOfDeletion <- Stream.from(1).take(a.length - sameStart.length)
                  lookingFor = a.drop(sameStart.length + sizeOfDeletion)
                  indexOfLookingFor = (if(lookingFor.length > 0) out.indexOfSlice(lookingFor, sameStart.length)
                                       else sameStart.length)
                  if indexOfLookingFor != -1
                  t = indexOfLookingFor + lookingFor.length
                  y <- flattenRev(q, out.drop(t))
              } yield (out.take(t)::y)
            }
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

case class MapReverse[A, B](fr: A ~~> B) extends (List[A] ~~> List[B]) {
  val f: A => B = fr.get _
  val fRev = (in: Option[A], b: B) => fr.put(b, in).toList
  def get(in: Input) = map(in)
  def put(out2: Output, in: Option[Input]): Constraint[Input] = Implicits.report(s"MapReverse.put($out2, $in) = %s"){
    in match {
    case None => mapRev(Nil, out2)
    case Some(in) => mapRev(in, out2)
  }
  }

  def map(l: List[A]): List[B] = l map f
  
  def combinatorialMap(l: List[B]): List[List[A]] = report(s"combinatorialMap($l)=%s"){
    l match {
      case Nil => List(Nil)
      case a::b => 
        fRev(None, a).flatMap(fb => combinatorialMap(b).map(fb::_))
    }
  }
  
  def mapRev(l: List[A], out: List[B]): List[List[A]] = {
    l match {
      case Nil => 
        out match {
          case Nil => List(Nil)
          /*case outhd::Nil => fRev(outhd).map(List(_))*/
          case outhd::outtail => 
            val revOutHd = fRev(None, outhd)
            for{ sol <- mapRev(l, outtail)
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
           val revOutHd = fRev(Some(hd), outhd)
           val p = revOutHd.filter(_ == hd)
           if(p.isEmpty) { // Looking for a deleted element maybe ?
             val expectedOut = l map f
             val k = expectedOut.indexOfSlice(out)
             if(k > 0) { // There has been a deletion, but we are able to find the remaining elements.
               mapRev(l.drop(k), out)
             } else {
               val k2 = out.indexOfSlice(expectedOut)
               if (k2 > 0) { // Some elements were added at some point.
                 val tailSolutions = mapRev(l, out.drop(k2))
                 // Now for each of out.take(k2), we take all possible inverses.
                 combinatorialMap(out.take(k2)).flatMap(l => tailSolutions.map(l ++ _))
               } else {
                 revOutHd.flatMap(s => mapRev(tl, outtail).map(s::_))
               }
             }
           } else {
             p.flatMap(s => mapRev(tl, outtail).map(s::_))
           }
       }
    }
  }// ensuring res => res.forall(sol => map(sol, f) == out && lehvenstein(l, sol) == lehvenstein(out, map(sol, f)))
}

case class FilterReverse[A](f: A => Boolean) extends (List[A] ~~> List[A]) {
  def get(in: Input) = filter(in, f)
  def put(out2: Output, in: Option[Input]) = Implicits.report(s"FilterReverse.put($out2, $in) = %s"){in match {
    case None => filterRev(Nil, f, out2)
    case Some(in) => filterRev(in, f, out2)
  }
  }

  def filter(l: List[A], f: A => Boolean): List[A] = l filter f
  
  def filterRev(l: List[A], f: A => Boolean, out: List[A]): List[List[A]] = {
    if (l.filter(f) == out) List(l) else
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

case class FlatMap[A, B](fr: A ~~> List[B]) extends (List[A] ~~> List[B]) {
  val f = fr.get _
  val fRev = (x: List[B]) => fr.put(x, None).toList // TODO: replace None by something clever.
  def get(in: Input) = flatMap(in, f)
  def put(out2: Output, in: Option[Input]) = flatMapRev(in.toList.flatten, f, fRev, out2)

  def flatMap(l: List[A], f: A => List[B]): List[B] = l.flatMap(f)

  def flatMapRev(l: List[A], f: A => List[B], fRev: List[B] => List[A], out: List[B]): List[List[A]] = {
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

case class Const[A](value: A) extends (Unit ~~> A) {
  def get(u: Unit) = value
  def put(output: A, orig: Option[Unit]): Stream[Unit] = Stream(())
}
*/
case class Id[A: Constrainable]() extends (A ~~> A) {
  def get(a: A) = a
  def put(out: A, orig: Option[A]) = Stream(out)
  def put(varIn: Variable, varOut: Variable, in: Option[A]) = {
    Constraint(varIn === varOut)
  }
}
/*
case class CastUp[A, B, B2 >: B](f: A ~~> B) extends (A ~~> B2) {
  def get(a: A) = f.get(a)
  def put(out: B2, orig: Option[A]) = {
    f.put(out.asInstanceOf[B], orig)
  }
}*/
