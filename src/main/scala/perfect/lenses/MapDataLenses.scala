package perfect.lenses
import perfect.core._
import perfect.core.predef._
import inox.trees.{FiniteSet, SetAdd}
import perfect.InoxProgramUpdater
import inox.trees.{FiniteMap, MapApply}
import scala.collection.mutable.ListBuffer

/**
  * Created by Mikael on 10/05/2017.
  */
trait MapDataLenses { self: InoxProgramUpdater.type =>
  def mkValueVar(name: String, m: FiniteMap): Var

  object MapDataLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      in.exp match {
        case l: FiniteMap =>
          if(isValue(l) && out.simplifiedExpr.isInstanceOf[FiniteMap]) {
            def reoderIfCanReorder(fm: FiniteMap) = {
              if(fm.pairs.forall(x => isValue(x._1))) { // Check that all the keys are values.
                val inserted = fm.pairs.filter(x => l.pairs.forall(y => x._1 != y._1))
                val fmUpdated = FiniteMap(l.pairs.flatMap {
                  case (key, value) => fm.pairs.collectFirst { case (k, v) if k == key => key -> v }
                } ++ inserted, fm.default, fm.keyType, fm.valueType)
                Stream(out.subExpr(fmUpdated))
              } else Stream(out)
            }
            reoderIfCanReorder(out.simplifiedExpr.asInstanceOf[FiniteMap])
          } else {
            // Check for changed keys, removals and additions.
            lazy val partEvaledPairs = l.pairs.map{ case (key, value) =>
              in.context.assignments.map(assign => (maybeEvalWithCache(assign(key)).getOrElse(throw new Exception(s"Could not evaluate ${assign(key)}")),
                (key, value, maybeEvalWithCache(assign(value)).getOrElse(throw new Exception(s"Could not evaluate ${assign(value)}"))))).getOrElse{
                throw new Exception(s"Could not evaluate assignments of $in")
              }
            }
            def propagateChange(fm: FiniteMap) = {
              val insertedPairs = fm.pairs.collect {
                case (k, v) if !partEvaledPairs.exists(x => x._1 == k) =>
                  Stream((k, ContExp(v)))
              }

              val (newFiniteMapKV) = (ListBuffer[Stream[(Exp, ContExp)]]() /: partEvaledPairs) {
                case (lb, (key_v, (key, value, value_v))) =>
                  val i = fm.pairs.lastIndexWhere(_._1 == key_v)
                  if(i > -1) {
                    val newValue = fm.pairs(i)._2
                    lb += repair(in.subExpr(value), out.subExpr(newValue)).map(pf => (key, pf))
                  } else {
                    lb
                  }
              }.toList ++ insertedPairs
              for {solution <- inox.utils.StreamUtils.cartesianProduct(newFiniteMapKV)
                   (mapKeys, mapValuesCont) = solution.unzip
                   mapValues = mapValuesCont.map(_.exp)
                   mapCont = mapValuesCont.map(_.context)
                   context = (Cont() /: mapCont){ case (f, ff) => f combineWith ff }
              } yield {
                ContExp(FiniteMap(mapKeys.zip(mapValues), l.default, l.keyType, l.valueType), context)
              }
            }
            out.simplifiedExpr match {
              case fm: FiniteMap => propagateChange(fm)
              case _ =>
                // We output the constraints with the given FiniteMap description.
                // We repair symbolically on every map's value.
                val repairs = partEvaledPairs.map {
                  case (key_v, (key, value, value_v)) =>
                    repair(in.subExpr(value), out.subExpr(MapApply(out.exp, key))).map((key_v, _))
                }
                for {keys_pf_seq <- inox.utils.StreamUtils.cartesianProduct(repairs)} yield {
                  val (keys, pf_seq) = keys_pf_seq.unzip
                  val (list_m, context) = ContExp.combineResults(pf_seq)
                  val new_exprs = keys.zip(list_m).toMap
                  // Keep the original order.
                  val newPairs = (partEvaledPairs map {
                    case (key_v, (key, value, value_v)) => key -> new_exprs(key_v)
                  })
                  ContExp(
                    FiniteMap(newPairs, l.default, l.keyType, l.valueType),
                    context)
                }
              //case _ => throw new Exception("Don't know what to do, not a Literal or a Variable: " + newOut)
            }

          }
        case MapApply(map, key) => // Variant of ADT selection.
          val map_v = in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(map))).getOrElse(return Stream.empty).asInstanceOf[FiniteMap] //originalAdtValue
          val key_v = in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(key))).getOrElse(return Stream.empty)

          val defaultValue = map_v.default

          val vds = map_v.pairs.map{ case (k, v) => (k, mkValueVar("x", map_v))}
          var found = false
          val constraints = (vds map {
            case (k, vd) => if(k == key_v) {
              found = true
              vd -> StrongValue(out.exp)
            } else {
              vd -> OriginalValue(maybeEvalWithCache(MapApply(map_v, k)).getOrElse(return Stream.empty))
            }
          }).toMap
          val finiteMapRepair = if (!found) { // We should not change the default, rather add a new entry.
            FiniteMap(vds.map{x => (x._1, x._2)} :+ (key_v -> out.exp)
              , map_v.default, map_v.keyType, map_v.valueType)
          } else {
            FiniteMap(vds.map{x => (x._1, x._2)}, map_v.default, map_v.keyType, map_v.valueType)
          }

          val newConstraint = Cont(constraints)

          for{ pf <- repair(in.subExpr(map), out.subExpr(finiteMapRepair) combineWith newConstraint) } yield {
            pf.wrap(x => MapApply(x, key))
          }

        case _ => Stream.Empty
      }
    }
  }
}
