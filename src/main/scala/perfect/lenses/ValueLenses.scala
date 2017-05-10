package perfect.lenses

import perfect.InoxProgramUpdater
import inox.trees.FunctionInvocation

/**
  * Created by Mikael on 09/05/2017.
  */
trait ValueLenses
  extends PatternMatchLenses
     with PatternReplaceLenses
     with ListInsertLenses
     with PasteVariableLenses
     with StringInsertLenses { self: InoxProgramUpdater.type =>

  def functionInvocationLens: SemanticLens

  val valueLenses = ShortcutGoal(Map(
    PatternMatchGoal.id -> PatternMatchLens,
    PatternReplaceGoal.id -> PatternReplaceLens,
    ListInsertGoal.id -> ListInsertLens,
    PasteVariableGoal.id -> PasteVariableLens,
    StringInsertGoal.id -> StringInsertLens
  ), {(e: Exp) =>
    e match {
      case FunctionInvocation(id, _, _) => Some(id)
      case _ => None
    }
  }) andThen combine(
    functionInvocationLens,
    FunctionInvocationUnificationLens)

/*
  (  // Stand-alone programs on how to repair the program for a given instruction
      functionInvocationLens) andThen // Matcher for function invocation in out.
    (FunctionInvocationUnificationLens andThen // Unification of arguments for function invocation.
      SetLens) andThen // Matchers for Set and SetApply constructions
    (MapDataLens andThen // Matcher for FiniteMap and MapApply constructions
      ADTExpr.Lens) // Matcher for ADT and ADTSelector constructions.
      */
}
