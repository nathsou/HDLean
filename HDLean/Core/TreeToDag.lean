import HDLean.Core.DagBuilder

/-!
# Tree circuits compile to node graphs

Expression-tree circuits (`Circuit`, written with `treeCircuit do` or by hand) are
translated to the node graph `Dag` by the proved builder. The theorem
`Circuit.toDag_correct` holds for every circuit, so every tree design reaches the
proved emitter without a per-design validator.

The translation does not recover sharing that exists only in memory: a subtree
used twice becomes two node sequences. Designs whose size depends on such sharing
should be written with the node-allocating `circuit do` instead.
-/

set_option backward.isDefEq.respectTransparency false

namespace HDLean
namespace Dag.Build

theorem input_ensures (s : State d i r) (k : Fin i) :
    Ensures s (input k) (fun j t => Refines t j (.input k)) := emit_ensures _ _ trivial

/-- Emit one node per tree constructor, children first. -/
def buildExpr : Expr d i r → M d i r Ref
  | .lit b => literal b
  | .input k => input k
  | .reg k => reg k
  | .inv a => do inv (← buildExpr a)
  | .and a b => do
    let x ← buildExpr a
    let y ← buildExpr b
    and x y
  | .xor a b => do
    let x ← buildExpr a
    let y ← buildExpr b
    xor x y
  | .mux c a b => do
    let x ← buildExpr c
    let y ← buildExpr a
    let z ← buildExpr b
    mux x y z

theorem buildExpr_ensures (e : Expr d i r) (s : State d i r) :
    Ensures s (buildExpr e) (fun j t => Refines t j e) := by
  induction e generalizing s with
  | lit b => exact literal_ensures s b
  | input k => exact input_ensures s k
  | reg k => exact reg_ensures s k
  | inv a iha =>
    apply ensures_bind (iha s)
    intro x t _ hx
    exact inv_ensures hx
  | and a b iha ihb =>
    apply ensures_bind (iha s)
    intro x t _ hx
    apply ensures_bind (ihb t)
    intro y u hu hy
    exact and_ensures (hx.mono hu) hy
  | xor a b iha ihb =>
    apply ensures_bind (iha s)
    intro x t _ hx
    apply ensures_bind (ihb t)
    intro y u hu hy
    exact xor_ensures (hx.mono hu) hy
  | mux c a b ihc iha ihb =>
    apply ensures_bind (ihc s)
    intro x t _ hx
    apply ensures_bind (iha t)
    intro y u hu hy
    apply ensures_bind (ihb u)
    intro z v hv hz
    exact mux_ensures ((hx.mono hu).mono hv) (hy.mono hv) hz

/-- The whole circuit: every register's next state, then every output. -/
def buildCircuit (c : Circuit d i r o) : M d i r (Vector Ref r × Vector Ref o) := do
  let next ← tabulate fun k : Fin r => buildExpr c.state[k].next
  let out ← tabulate fun k : Fin o => buildExpr c.output[k]
  pure (next, out)

theorem buildCircuit_ensures (c : Circuit d i r o) :
    Ensures empty (buildCircuit c) (fun p t =>
      (∀ k : Fin r, Refines t p.1[k] c.state[k].next) ∧ WordRefines t p.2 c.output) := by
  apply ensures_bind (tabulate_ensures (fun k : Fin r => buildExpr c.state[k].next)
    (fun k j t => Refines t j c.state[k].next) (fun _ _ _ _ he h => h.mono he) empty
    (fun t _ k => buildExpr_ensures _ t))
  intro next t _ hn
  apply ensures_bind (tabulate_ensures (fun k : Fin o => buildExpr c.output[k])
    (fun k j t => Refines t j c.output[k]) (fun _ _ _ _ he h => h.mono he) t
    (fun u _ k => buildExpr_ensures _ u))
  intro out u hu ho
  apply ensures_pure
  exact ⟨fun k => (hn k).mono hu, fun k => ho k⟩

end Dag.Build

namespace Circuit

theorem toDag_exists (c : Circuit d i r o) :
    ∃ dag, Dag.Build.run c.name (c.state.map (·.reset)) (Dag.Build.buildCircuit c) = some dag ∧
      (∀ s xs, dag.nextState s xs = c.next s xs) ∧
      (∀ s xs, dag.evalOutput s xs = c.evalOutput s xs) :=
  Dag.Build.run_implements c _ (Dag.Build.buildCircuit_ensures c)

/-- The node graph of a tree circuit, keeping its port and register names. The builder never fails on a tree (the
`toDag_exists` theorem), so the fallback branch is unreachable. -/
def toDag (c : Circuit d i r o) : Dag d i r o :=
  match h : Dag.Build.run c.name (c.state.map (·.reset)) (Dag.Build.buildCircuit c) with
  | some dag => { dag with
      inputNames := c.inputNames, outputNames := c.outputNames
      stateNames := c.state.map (·.name), sources := c.state.map (·.source) }
  | none => False.elim (by
      obtain ⟨_, hd, _⟩ := toDag_exists c
      rw [h] at hd
      cases hd)

theorem toDag_nextState (c : Circuit d i r o) (s xs) : c.toDag.nextState s xs = c.next s xs := by
  unfold toDag
  split
  · rename_i dag h
    obtain ⟨dag', hd, hn, _⟩ := toDag_exists c
    rw [h] at hd
    cases hd
    exact hn s xs
  · rename_i h
    exact absurd h (by obtain ⟨_, hd, _⟩ := toDag_exists c; rw [hd]; simp)

theorem toDag_evalOutput (c : Circuit d i r o) (s xs) : c.toDag.evalOutput s xs = c.evalOutput s xs := by
  unfold toDag
  split
  · rename_i dag h
    obtain ⟨dag', hd, _, ho⟩ := toDag_exists c
    rw [h] at hd
    cases hd
    exact ho s xs
  · rename_i h
    exact absurd h (by obtain ⟨_, hd, _⟩ := toDag_exists c; rw [hd]; simp)

end Circuit
end HDLean
