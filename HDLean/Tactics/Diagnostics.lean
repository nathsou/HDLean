import HDLean.Verification.Invariant
import Lean

open Lean Elab Tactic Meta

/-- Render the actual remaining proof obligations without changing them. -/
elab "hw_goal" : tactic => do
  for goal in ← getGoals do
    logInfo m!"HDLean obligation:\n{goal}"

/-- Evaluate explicit finite samples before attempting an inductive relation.
This diagnostic creates no proof term and adds no axiom. -/
elab "refute_small " samples:term " with " predicate:term : tactic => do
  let expression ← Term.elabTerm (← `(HDLean.Verification.refuteSmall $samples $predicate))
    (some (mkConst ``String))
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let result ← unsafe Meta.evalExpr String (mkConst ``String) expression
  if result != "" then throwError "{result}"

/-- Finite reachability is an interchangeable oracle for fixed small instances.
The suggestion must still pass the generic kernel-checkable inductiveness test. -/
macro "invariant? " system:term ", " fuel:term : command =>
  `(command| #eval HDLean.Verification.FiniteSystem.suggest $system $fuel)

