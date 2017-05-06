package perfect
package lenses
import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.ReverseProgram.{Cache, repair, maybeEvalWithCache}
import perfect.Utils.isValue

import scala.collection.mutable.ListBuffer

/**
  * Created by Mikael on 05/05/2017.
  */
object MapDataLens extends semanticlenses.SemanticLens {
  def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    in.expr match {
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
            in.formula.assignments.map(assign => (maybeEvalWithCache(assign(key)).getOrElse(throw new Exception(s"Could not evaluate ${assign(key)}")),
              (key, value, maybeEvalWithCache(assign(value)).getOrElse(throw new Exception(s"Could not evaluate ${assign(value)}"))))).getOrElse{
              throw new Exception(s"Could not evaluate assignments of $in")
            }
          }
          def propagateChange(fm: FiniteMap) = {
            val insertedPairs = fm.pairs.collect {
              case (k, v) if !partEvaledPairs.exists(x => x._1 == k) =>
                Stream((k, ProgramFormula(v)))
            }

            val (newFiniteMapKV) = (ListBuffer[Stream[(Expr, ProgramFormula)]]() /: partEvaledPairs) {
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
                 (mapKeys, mapValuesFormula) = solution.unzip
                 mapValues = mapValuesFormula.map(_.expr)
                 mapFormula = mapValuesFormula.map(_.formula)
                 formula = (Formula() /: mapFormula){ case (f, ff) => f combineWith ff }
            } yield {
              ProgramFormula(FiniteMap(mapKeys.zip(mapValues), l.default, l.keyType, l.valueType), formula)
            }
          }
          out.simplifiedExpr match {
            case fm: FiniteMap => propagateChange(fm)
            case _ =>
              // We output the constraints with the given FiniteMap description.
              // We repair symbolically on every map's value.
              val repairs = partEvaledPairs.map {
                case (key_v, (key, value, value_v)) =>
                  repair(in.subExpr(value), out.subExpr(MapApply(out.expr, key))).map((key_v, _))
              }
              for {keys_pf_seq <- inox.utils.StreamUtils.cartesianProduct(repairs)} yield {
                val (keys, pf_seq) = keys_pf_seq.unzip
                val (list_m, formula) = ProgramFormula.combineResults(pf_seq)
                val new_exprs = keys.zip(list_m).toMap
                // Keep the original order.
                val newPairs = (partEvaledPairs map {
                  case (key_v, (key, value, value_v)) => key -> new_exprs(key_v)
                })
                ProgramFormula(
                  FiniteMap(newPairs, l.default, l.keyType, l.valueType),
                  formula)
              }
            //case _ => throw new Exception("Don't know what to do, not a Literal or a Variable: " + newOut)
          }

        }
      case MapApply(map, key) => // Variant of ADT selection.
        val map_v = maybeEvalWithCache(in.formula.assignments.get(map)).getOrElse(return Stream.empty).asInstanceOf[FiniteMap] //originalAdtValue
        val key_v = maybeEvalWithCache(in.formula.assignments.get(key)).getOrElse(return Stream.empty)

        val defaultValue = map_v.default

        val vds = map_v.pairs.map{ case (k, v) => (k, Variable(FreshIdentifier("x", true), map_v.valueType, Set()))}
        var found = false
        val constraints = (vds map {
          case (k, vd) => if(k == key_v) {
            found = true
            vd -> StrongValue(out.expr)
          } else {
            vd -> OriginalValue(maybeEvalWithCache(MapApply(map_v, k)).getOrElse(return Stream.empty))
          }
        }).toMap
        val finiteMapRepair = if (!found) { // We should not change the default, rather add a new entry.
          FiniteMap(vds.map{x => (x._1, x._2)} :+ (key_v -> out.expr)
            , map_v.default, map_v.keyType, map_v.valueType)
        } else {
          FiniteMap(vds.map{x => (x._1, x._2)}, map_v.default, map_v.keyType, map_v.valueType)
        }

        val newConstraint = Formula(constraints)

        for{ pf <- repair(in.subExpr(map), out.subExpr(finiteMapRepair) combineWith newConstraint) } yield {
          pf.wrap(x => MapApply(x, key))
        }

      case _ => Stream.Empty
    }
  }
}
