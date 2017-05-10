package perfect.lenses

import inox.FreshIdentifier
import perfect.InoxProgramUpdater
import inox.trees._
import perfect.core.predef.{ADTLenses, ListInsertLenses, MapDataLenses, SetLenses}
import perfect.semanticlenses.ListInsertGoal

/**
  * Created by Mikael on 09/05/2017.
  */
trait ValueLenses
  extends PatternMatchLenses
     with PatternReplaceLenses
     with ListInsertLenses
     with PasteVariableLenses
     with StringInsertLenses
     with SetLenses
     with MapDataLenses
     with ADTLenses { self: InoxProgramUpdater.type =>

  def functionInvocationLens: SemanticLens

  private val setId = FreshIdentifier("setop")
  private val mapId = FreshIdentifier("mapop")
  private val adtId = FreshIdentifier("adtop")

  val valueLenses = ShortcutGoal(Map(
    PatternMatchGoal.id -> PatternMatchLens,
    PatternReplaceGoal.id -> PatternReplaceLens,
    ListInsertGoal.id -> ListInsertLens,
    PasteVariableGoal.id -> PasteVariableLens,
    StringInsertGoal.id -> StringInsertLens,
    setId -> SetLens,
    mapId -> MapDataLens,
    adtId -> ADTLens
  ), {(in: Exp) =>
    in match {
      case FunctionInvocation(id, _, _) => Some(id)
      case _: SetAdd | _: FiniteSet => Some(setId)
      case _: MapApply | _: FiniteMap => Some(mapId)
      case _: ADTSelector | _: ADT => Some(adtId)
      case _ => None
    }
  }) andThen combine(
    functionInvocationLens, // Matcher for function invocation in out.
    FunctionInvocationUnificationLens) // Unification of arguments for function invocation.
}
