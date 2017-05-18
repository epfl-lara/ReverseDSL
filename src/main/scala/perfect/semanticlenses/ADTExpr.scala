package perfect
package semanticlenses

import inox._
import inox.trees._
import inox.trees.dsl._
import perfect.ProgramFormula.{CustomProgramFormula, MergeProgramFormula}
import perfect.ReverseProgram.{Cache, maybeEvalWithCache, repair}
import perfect.StringConcatExtended._

/**
  * Created by Mikael on 04/05/2017.
  */
object ADTExpr extends CustomProgramFormula with MergeProgramFormula {
  object Eval {
    def unapply(e: Expr)(implicit symbols: Symbols) = e match {
      case e@ADT(_, _) => Some(e)
      case _ => None
    }
  }
  var xCounter = 1

  object Lens extends SemanticLens {
    override def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
      in.expr match {
        case ADT(adtType@ADTType(tp, tpArgs), argsIn) =>
          out.simplifiedExpr match {
            case outExpr@ADT(ADTType(tp2, tpArgs2), argsOut) if tp2 == tp && tpArgs2 == tpArgs && in.getFunctionValue != Some(outExpr) => // Same type ! Maybe the arguments will change or move.
              //Log("ADT 2")
              val argsInValue = in.getFunctionValue match {
                case Some(ADT(ADTType(_, _), argsInValue)) => argsInValue.map(x => Some(x))
                case _ => argsIn.map(_ => None)
              }

              val seqOfStreamSolutions = (argsIn.zip(argsInValue)).zip(argsOut).map { case ((aFun, aFunVal), newOutArg) =>
                repair(ProgramFormula(aFun, in.formula).withComputedValue(aFunVal), out.subExpr(newOutArg))
              }
              val streamOfSeqSolutions = inox.utils.StreamUtils.cartesianProduct(seqOfStreamSolutions)
              for {seq <- streamOfSeqSolutions
                   //_ = Log(s"combineResults($seq)")
                   (newArgs, assignments) = ProgramFormula.combineResults(seq)
              } yield {
                ProgramFormula(ADT(ADTType(tp2, tpArgs2), newArgs), assignments)
              }
            case _: Variable | ADT(ADTType(_, _), _) =>
              Stream(out)

            case a =>
              Log(s"[Warning] Don't know how to handle this case : $a is supposed to be put in place of a ${tp}")
              Stream(out)
          }

        case as@ADTSelector(adt, selector) =>
          val originalAdtValue = in.formula.assignments.flatMap(assign => maybeEvalWithCache(assign(adt))).getOrElse(return Stream.empty).asInstanceOf[ADT]
          val constructor = as.constructor.get
          val fields = constructor.fields
          val index = as.selectorIndex
          val vrs = fields.map { fd => Variable(FreshIdentifier("x"+ { xCounter += 1; xCounter }, false), fd.getType, Set()) }
          val constraints = vrs.zipWithIndex.map {
            case (vd, i) => vd -> (if (i == index) StrongValue(out.expr) else OriginalValue(originalAdtValue.args(i)))
          }.toMap
          val newConstraint = Formula(constraints)

          for {pf <- repair(in.subExpr(adt),
            out.subExpr(ADT(ADTType(constructor.id, constructor.tps), vrs)) combineWith newConstraint)} yield {
            pf.wrap(x => ADTSelector(x, selector))
          }
        case _ => Stream.empty
      }
    }
  }
  def merge(e1: Expr, e2: Expr)(implicit symbols: Symbols): Option[(Expr, Seq[(Variable, KnownValue)])] = e2 match {
    case e2@ADT(tpe, vars1) if vars1.forall(_.isInstanceOf[Variable]) =>
      e1 match {
        case ADT(tpe2, vars2) if vars2.forall(_.isInstanceOf[Variable]) && tpe == tpe2 =>
          val vvars1: Seq[Variable] = vars1.collect { case v: Variable => v }
          val vvars2: Seq[Variable] = vars2.collect { case v: Variable => v }
          Some((e1, vars1.zip(vvars2).map{ case (x1: Variable, x2: Variable) =>
              x1 -> StrongValue(x2)
          }))
        case _ => None
      }
    case _ => None
  }


  object Goal extends FunDefGoal {
    def funDef = mkFunDef(FreshIdentifier("ADT"))("A"){ case Seq(tA) =>
      (Seq("id"::tA), tA,
        { case Seq(id) =>
          id // Dummy
        })
    }
  }

}
