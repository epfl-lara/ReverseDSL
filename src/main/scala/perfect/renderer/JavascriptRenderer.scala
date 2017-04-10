package perfect
package renderer

import inox._
import inox.trees._
import inox.trees.dsl._
import org.apache.commons.lang3.StringEscapeUtils

/**
  * Created by Mikael on 27/03/2017.
  */
object JavascriptRenderer extends inox.ast.Printer {
  val trees = inox.trees

  var printTypes = false
  var useLambdaArrows = true
  private val q = "\""
  private val t = "`"

  /** For the real javascript use these definitions*/
  var jsdefs =
    """let Map = function(dflt) {
      |  let res = new Proxy({}, { get: function(target, name) { return target.hasOwnProperty(name) ? target[name] : dflt; }})
      |  for(var i = 1; i < arguments.length; i++) {
      |    res[arguments[i][0]] = arguments[i][1]
      |  }
      |  return res;
      |}
    """.stripMargin

  object StringConcats {
    private object StringConcatExtract {
      def unapply(e: Expr): Some[List[Expr]] = e match {
        case StringConcat(StringConcatExtract(a), StringConcatExtract(b)) => Some(a ++ b)
        case e => Some(List(e))
      }
    }

    def unapply(e: Expr): Option[List[Expr]] = e match {
      case StringConcatExtract(l) if l.length >= 2 => Some(l)
      case _ => None
    }
  }

  override protected def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case fm @ FiniteMap(rs, dflt, _, _) =>
      p"""Map($dflt"""
      if(rs.isEmpty) {
        p""")"""
      } else {
        nary(rs.map{case (k, v) => ListLiteral(List(k, v), UnitType)}, ",\n|", ",\n|", ")").print(ctx.copy(lvl = ctx.lvl + 1))
      }
    case vd @ ValDef(id, tpe, flags) =>
      if (flags.isEmpty) {
        if(printTypes) p"$id/*: $tpe*/" else p"$id"
      } else {
        if(printTypes) p"$id/*: $tpe*/" else p"$id"
        p"($id/*: $tpe*/)"
        for (f <- flags) p" /*${f.asString(ctx.opts)}*/"
      }
    case Lambda(args, body) =>
      if(useLambdaArrows) {
        optP {
          p"($args) => $body"
        }
      } else {
        optP {
          p"function($args) { return $body }"
        }
      }
    case Not(Equals(a, b)) => p"$a !== $b"
    case Equals(a, b) => p"$a === $b"
    case Let(c:ValDef, AsInstanceOf(v: Variable, ADTType(Utils.cons, Seq(t))), body) => // No need for let-def printing.
      ppBody(exprOps.replaceFromSymbols(Map(c -> v), body))
    case Let(b, d, e) =>
      p"""|let $b = $d
          |$e"""
    case ADTSelector(e, Utils.head) => p"$e[0]"
    case ADTSelector(e, Utils.tail) => p"$e.slice(1)"
    case ListLiteral(l, tpe) =>
      nary(l, ", ", "[", "]").print(ctx)
    case e @ ADT(adt, args) =>
      p"new $adt($args)"
    case MapApply(a, i) =>
      p"$a[$i]"
    case StringConcats(ss) if ss.exists(_.isInstanceOf[StringLiteral]) => // Use tick printing.
      p"`"
      for(s <- ss) {
        s match {
          case StringLiteral(v) =>
            val escaped = v.replaceAllLiterally("\\", "\\\\").replaceAllLiterally("`", "\\`") // We can keep newlines !
            ctx.sb append escaped // We appen the string raw.
          case e => p"$${$e}"
        }
      }
      p"`"

    case StringConcat(StringConcat(a, sl@StringLiteral(s)), b) if s.endsWith("\n") => // Is not used anymore normally
      p"""$a + $sl +
         |$b"""
    case IsInstanceOf(e, ADTType(Utils.nil, Seq())) => p"$e.length === 0"
    case IsInstanceOf(e, ADTType(Utils.cons, Seq(t))) => p"$e.length > 0"
    case AsInstanceOf(e, ADTType(Utils.cons, Seq(t))) => p"""$e"""
    case AsInstanceOf(e, ct) => p"""$e"""
    case IsInstanceOf(e, cct) => p"$e.tag === $q$cct$q"
    case FunctionInvocation(id, tps, args) =>
      p"$id($args)"
    case StringLiteral(v) =>
      val escaped = v.replaceAllLiterally("\\", "\\\\").replaceAllLiterally("`", "\\`") // We can keep newlines !
      p"$t$escaped$t"
    case _ => super.ppBody(tree)
  }
}
