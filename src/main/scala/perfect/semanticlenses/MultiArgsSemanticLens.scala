package perfect
package semanticlenses

import inox.trees._
import perfect.ReverseProgram.Cache

/**
  * Created by Mikael on 09/05/2017.
  */
trait MultiArgsSemanticLens extends SemanticLens with MultipleArgExtractor {
  def put(in: ProgramFormula, out: ProgramFormula)(implicit symbols: Symbols, cache: Cache): Stream[ProgramFormula] = {
    extract(in.expr) match {
      case Some((args, wrapper, build)) =>
        in.formula.partialAssignments.map(_._1) match {
          case Some(assign) =>
            val argsOptValue = args.map(arg => ReverseProgram.maybeEvalWithCache(assign(arg)))
            if (argsOptValue.forall(_.nonEmpty)) {
              val argsFormulas = argsOptValue.map(x => in.subExpr(x.get))
              val lenseResult = wrapper(argsFormulas, out)
              for {l <- lenseResult; (newArgsValues, newForm) = l
                   a <- ProgramFormula.repairArguments(in.formula, args.zip(newArgsValues))
                   (newArguments, newArgumentsFormula) = a
              } yield {
                val formula = newForm combineWith newArgumentsFormula
                ProgramFormula(build(newArguments), formula)
              }
            }
            else Stream.empty
          case None => Stream.empty
        }

      case _ => Stream.empty
    }
  }
  isPreemptive = false
}