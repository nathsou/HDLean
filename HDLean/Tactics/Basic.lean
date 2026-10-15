import HDLean.Tactics.Attr
import HDLean.Semantics.Composition
import HDLean.Netlist.Lower
import Std.Tactic.BVDecide

attribute [circuit_simp] HDLean.Expr.eval HDLean.Expr.eval_or
  HDLean.PMachine.stateFrom_zero HDLean.PMachine.stateFrom_succ
  HDLean.Machine.stateAt_zero HDLean.Machine.stateAt_succ HDLean.lowerExpr_correct

/-- Kernel-only automation never invokes native bit-blasting. -/
macro "hw_step_kernel" : tactic => `(tactic|
  (simp only [circuit_simp] at *
   repeat' split
   all_goals first | rfl | omega | grind))

/-- Development/review automation; its native-evaluation axioms are audited per theorem. -/
macro "hw_step" : tactic => `(tactic|
  (simp only [circuit_simp] at *
   repeat' split
   all_goals first | rfl | bv_decide | omega | grind))

macro "simulation " r:term : tactic => `(tactic|
  apply HDLean.refinesAfterReset_of_simulation _ _ _ _ $r)
macro "hw_cases " h:ident : tactic => `(tactic| cases ($h) <;> simp_all)
macro "compose" : tactic => `(tactic| apply HDLean.compose_contracts)
macro "nonint" : tactic => `(tactic| apply HDLean.reset_noninterference)
macro "k_induction " k:term : tactic => `(tactic| apply HDLean.k_induction _ $k)
