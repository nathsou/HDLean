import HDLean.Backend.DagEmit
import HDLean.Backend.Validate
import HDLean.Backend.AigerBinary

/-!
# Emission of externally optimised graphs

`Format.emitWith f c h cert` emits `h`'s logic if `cert` proves it equivalent
to our lowering of `c`, and our lowering otherwise. `emitWith_correct` is the
same contract as `emit_correct`, for every `h` and `cert`: the optimiser and
the SAT solver can only make the output smaller, never wrong.
-/
namespace HDLean.Backend.Proved
open Validate

def Format.emitWith (f : Format) (c : Dag d i r o) (h : Graph) (cert : Array Std.Tactic.BVDecide.LRAT.IntAction) :
    String :=
  f.print (Aag.ofGraph (select (Dag.lowerOpt c) h cert))

theorem lowerOpt_inputs (c : Dag d i r o) : (Dag.lowerOpt c).inputs = i + 1 := by
  simp [Dag.lowerOpt, Dag.lowerTight]

theorem lowerOpt_latches (c : Dag d i r o) : (Dag.lowerOpt c).latches = r := by
  simp [Dag.lowerOpt, Dag.lowerTight]

theorem emitWith_correct (f : Format) (c : Dag d i r o) (h : Graph)
    (cert : Array Std.Tactic.BVDecide.LRAT.IntAction) (xs : Vector Bool i) (s : Vector Bool r) (rst : Bool) :
    f.meaning (f.emitWith c h cert) (xs.toArray.push rst) s.toArray = some
      ((Vector.ofFn (c.nextState (fun k => s[k]) ((fun k => xs[k]),rst))).toArray,
       (Vector.ofFn (c.evalOutput (fun k => s[k]) (fun k => xs[k]))).toArray) := by
  have hwf := select_wellFormed (Dag.lowerOpt c) h cert (Dag.lowerOpt_wellFormed c)
  unfold Format.meaning Format.parse Format.emitWith
  rw [Format.decode_print]
  dsimp only [Bind.bind, Option.bind]
  rw [canonical_wellFormed _ hwf]
  simp only [↓reduceIte, Option.map_some]
  have hn := Graph.next_size_of_wellFormed _ hwf
  rw [Graph.eval_eq_of_logic_eq _ _ (Aag.ofGraph_logic _ hn),
    select_eval _ _ _ _ _ (by simp [lowerOpt_inputs]) (by simp [lowerOpt_latches]), Dag.lowerOpt_correct]

end HDLean.Backend.Proved
