package perfect.lenses

import perfect.InoxProgramUpdater
import inox.trees.{ADT, ADTType, ADTSelector}

/**
  * Created by Mikael on 10/05/2017.
  */
trait ADTLenses { self: InoxProgramUpdater.type =>
  /** Returns a sequence of variable, the index of the selector and a builder */
  def freshVarsForConstructor(as: ADTSelector)(implicit symbols: Symbols): (Seq[Var], Int, Seq[Exp] => Exp)

  object ADTLens extends SemanticLens {
    override def put(in: ContExp, out: ContExp)(implicit symbols: Symbols, cache: Cache): Stream[ContExp] = {
      in.exp match {
        case ADT(adtType@ADTType(tp, tpArgs), argsIn) =>
          out.simplifiedExpr match {
            case outExpr@ADT(ADTType(tp2, tpArgs2), argsOut) if tp2 == tp && tpArgs2 == tpArgs && in.getFunctionValue != Some(outExpr) => // Same type ! Maybe the arguments will change or move.
              //Log("ADT 2")
              val argsInValue = in.getFunctionValue match {
                case Some(ADT(ADTType(_, _), argsInValue)) => argsInValue.map(x => Some(x))
                case _ => argsIn.map(_ => None)
              }

              val seqOfStreamSolutions = (argsIn.zip(argsInValue)).zip(argsOut).map { case ((aFun, aFunVal), newOutArg) =>
                repair(ContExp(aFun, in.context).withComputedValue(aFunVal), out.subExpr(newOutArg))
              }
              val streamOfSeqSolutions = inox.utils.StreamUtils.cartesianProduct(seqOfStreamSolutions)
              for {seq <- streamOfSeqSolutions
                  // _ = Log(s"combineResults($seq)")
                   (newArgs, assignments) = ContExp.combineResults(seq)
              } yield {
                ContExp(ADT(ADTType(tp2, tpArgs2), newArgs), assignments)
              }
            case Var(_) | ADT(ADTType(_, _), _) =>
              Stream(out)

            case a =>
              //Log(s"[Warning] Don't know how to handle this case : $a is supposed to be put in place of a ${tp}")
              Stream(out)
          }

        case as@ADTSelector(adt, selector) =>
          val originalAdtValue = in.context.assignments.flatMap(assign => maybeEvalWithCache(assign(adt))).getOrElse(return Stream.empty).asInstanceOf[ADT]
          val (vrs, index, builder) = freshVarsForConstructor(as)

          val constraints = vrs.zipWithIndex.map {
            case (vd, i) => vd -> (if (i == index) StrongValue(out.exp) else OriginalValue(originalAdtValue.args(i)))
          }.toMap

          for {pf <- repair(in.subExpr(adt),
            out.subExpr(builder(vrs)) combineWith Cont(constraints))} yield {
            pf.wrap(x => ADTSelector(x, selector))
          }
        case _ => Stream.empty
      }
    }
  }
}
