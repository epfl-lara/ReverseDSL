package perfect.lenses

import perfect.InoxProgramUpdater

/**
  * Created by Mikael on 09/05/2017.
  */
trait ValueLenses
  extends perfect.lenses.PatternMatchLenses { self: InoxProgramUpdater.type =>

  val valueLenses = PatternMatchLens // andThen
/*
  (  // Stand-alone programs on how to repair the program for a given instruction
    PatternReplaceLens) andThen
    (ListInsertLens andThen
      PasteVariableLens) andThen
    (StringInsertLens andThen
      functionInvocationLens) andThen // Matcher for function invocation in out.
    (FunctionInvocationUnificationLens andThen // Unification of arguments for function invocation.
      SetLens) andThen // Matchers for Set and SetApply constructions
    (MapDataLens andThen // Matcher for FiniteMap and MapApply constructions
      ADTExpr.Lens) // Matcher for ADT and ADTSelector constructions.
      */
}
