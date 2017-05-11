package perfect.core.predef

import perfect.core._

import scala.collection.mutable.ListBuffer

/**
  * Created by Mikael on 10/05/2017.
  */
trait MapDataLenses { self: ProgramUpdater with ContExps with Lenses =>
  /** Returns the pairs, the default and a builder*/
  def extractMap(e: Exp)(implicit symbols: Symbols): Option[(Seq[(Exp, Exp)], Exp, (Seq[(Exp, Exp)], Exp) => Exp)]

  // Returns the expression building the map and the one building the argument, and a function to create a variable of type the Map's value type
  def extractMapApply(e: Exp)(implicit symbols: Symbols): Option[(Exp, Exp, String => Var)]
  def buildMapApply(e: Exp, g: Exp): Exp

  private object MapData {
    def unapply(e: Exp) = extractMap(e)
  }

  private object MapDataApply {
    def unapply(e: Exp) = extractMapApply(e)
    def apply(e: Exp, g: Exp) = buildMapApply(e, g)
  }

  object MapDataLens extends SemanticLens {
    def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      in.exp match {
        case l@MapData(pairs, inDefault, inBuilder) =>
          out.simplifiedExpr match {
            case outMap@MapData(outPairs, outDefault, outBuilder) if isValue(l) =>
              if(outPairs.forall(x => isValue(x._1))) { // Check that all the keys are values.
                val inserted = outPairs.filter(x => pairs.forall(y => x._1 != y._1))
                val fmUpdated = outBuilder(pairs.flatMap {
                  case (key, value) => outPairs.collectFirst { case (k, v) if k == key => key -> v }
                } ++ inserted, outDefault)
                Stream(out.subExpr(fmUpdated))
              } else Stream(out)
            case _ =>
            // Check for changed keys, removals and additions.
            lazy val partEvaledPairs = pairs.map{ case (key, value) =>
              in.context.assignments.map(assign => (maybeEvalWithCache(assign(key)).getOrElse(throw new Exception(s"Could not evaluate ${assign(key)}")),
                (key, value, maybeEvalWithCache(assign(value)).getOrElse(throw new Exception(s"Could not evaluate ${assign(value)}"))))).getOrElse{
                throw new Exception(s"Could not evaluate assignments of $in")
              }
            }
            def propagateChange(fmpairs: Seq[(Exp, Exp)], fmdefault: Exp, fmbuilder: (Seq[(Exp, Exp)], Exp) => Exp) = {
              val insertedPairs = fmpairs.collect {
                case (k, v) if !partEvaledPairs.exists(x => x._1 == k) =>
                  Stream((k, ContExp(v)))
              }

              val (newFiniteMapKV) = (ListBuffer[Stream[(Exp, ContExp)]]() /: partEvaledPairs) {
                case (lb, (key_v, (key, value, value_v))) =>
                  val i = fmpairs.lastIndexWhere(_._1 == key_v)
                  if(i > -1) {
                    val newValue = fmpairs(i)._2
                    lb += repair(in.subExpr(value), out.subExpr(newValue)).map(pf => (key, pf))
                  } else {
                    lb
                  }
              }.toList ++ insertedPairs
              for {solution <- Utils.StreamUtils.cartesianProduct(newFiniteMapKV)
                   (mapKeys, mapValuesCont) = solution.unzip
                   mapValues = mapValuesCont.map(_.exp)
                   mapCont = mapValuesCont.map(_.context)
                   context = (Cont() /: mapCont){ case (f, ff) => f combineWith ff }
              } yield {
                ContExp(inBuilder(mapKeys.zip(mapValues), inDefault), context)
              }
            }
            out.simplifiedExpr match {
              case MapData(pairs, default, builder) => propagateChange(pairs, default, builder)
              case _ =>
                // We output the constraints with the given FiniteMap description.
                // We repair symbolically on every map's value.
                val repairs = partEvaledPairs.map {
                  case (key_v, (key, value, value_v)) =>
                    repair(in.subExpr(value), out.subExpr(MapDataApply(out.exp, key))).map((key_v, _))
                }
                for {keys_pf_seq <- Utils.StreamUtils.cartesianProduct(repairs)} yield {
                  val (keys, pf_seq) = keys_pf_seq.unzip
                  val (list_m, context) = ContExp.combineResults(pf_seq)
                  val new_exprs = keys.zip(list_m).toMap
                  // Keep the original order.
                  val newPairs = partEvaledPairs map {
                    case (key_v, (key, value, value_v)) => key -> new_exprs(key_v)
                  }
                  ContExp(inBuilder(newPairs, inDefault), context)
                }
              //case _ => throw new Exception("Don't know what to do, not a Literal or a Variable: " + newOut)
            }

          }
        case MapDataApply(map, key, mkValueVar) => // Variant of ADT selection.
          val map_v = in.maybeEval(map).getOrElse(return Stream.empty) //originalAdtValue
          val key_v = in.maybeEval(key).getOrElse(return Stream.empty)
          map_v match {
            case MapData(map_vpairs, defaultValue, builder) =>
              val vds = map_vpairs.map{ case (k, v) => (k, mkValueVar("x"))}
              var found = false
              val constraints = (vds map {
                case (k, vd) => if(k == key_v) {
                  found = true
                  vd -> StrongValue(out.exp)
                } else {
                  vd -> OriginalValue(maybeEvalWithCache(MapDataApply(map_v, k)).getOrElse(return Stream.empty))
                }
              }).toMap
              val finiteMapRepair = if (!found) { // We should not change the default, rather add a new entry.
                builder(vds.map{x => (x._1, x._2)} :+ (key_v -> out.exp), defaultValue)
              } else {
                builder(vds.map{x => (x._1, x._2)}, defaultValue)
              }

              val newConstraint = Cont(constraints)

              for{ pf <- repair(in.subExpr(map), out.subExpr(finiteMapRepair) combineWith newConstraint) } yield {
                pf.wrap(x => MapDataApply(x, key))
              }
            case _ => Stream.empty
          }


        case _ => Stream.Empty
      }
    }
  }
}
