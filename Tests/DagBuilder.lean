import Designs.Toy16.DagRefinement

namespace HDLean.Dag.Build.Tests

def sharedProgram : M 0 1 1 (Vector Ref 1 × Vector Ref 2) := do
  let a ← input ⟨0,by decide⟩
  let b ← xor a a
  let c ← inv b
  pure (#v[c],#v[b,c])

example : (run "shared" #v[.hold] sharedProgram).isSome = true := by decide +kernel
example : ((run "shared" #v[.hold] sharedProgram).map (fun c => c.nodes.length)) = some 3 := by decide +kernel
example : (emit (.not 0) (empty : State 0 1 1)) = none := by decide +kernel
example (s : State 0 1 1) :
    Ensures s (literal true) (fun j t => Refines t j (.lit true)) := literal_ensures s true

/-- Independent construction regression: all 16 opcodes, both reset phases,
arbitrary payload storage, and a changing instruction ROM. -/
def main : IO Unit := do
  let rom : Toy16.Addr → Toy16.Word := fun a => BitVec.ofNat 16 (a.toNat*491+7)
  let some c := Toy16.DagPhysical.hardware? rom | throw (IO.userError "DAG CPU construction failed")
  let graph := c.lower
  unless graph.wellFormed do throw (IO.userError "malformed DAG CPU graph")
  let tree := Toy16.Physical.hardware rom
  -- Reference: the tree circuit's own semantics, evaluated directly.
  let reference (rst : Bool) (st : Array Bool) : Array Bool × Array Bool :=
    let s : Fin (268*16) → Bool := fun k => st[k.val]!
    ((Vector.ofFn (tree.next s (Fin.elim0, rst))).toArray, (Vector.ofFn (tree.evalOutput s Fin.elim0)).toArray)
  for opcode in List.range 16 do
    let instruction : BitVec 16 := BitVec.ofNat 16 (opcode*4096+3*512+2*64+8+5)
    let state := (Vector.ofFn fun j : Fin (268*16) =>
      if 48 ≤ j.val ∧ j.val < 64 then instruction.getLsbD (j.val-48)
      else decide ((j.val*7919+opcode*104729)%13 < 6)).toArray
    for rst in [false,true] do
      unless graph.eval #[rst] state == reference rst state do
        throw (IO.userError s!"DAG CPU mismatch: opcode {opcode}, reset {rst}")
  let mut state := (Vector.ofFn fun j : Fin (268*16) => decide (j.val%7 < 3)).toArray
  for cycle in List.range 64 do
    let rst := cycle == 0 || cycle == 39
    let actual := graph.eval #[rst] state
    unless actual == reference rst state do
      throw (IO.userError s!"DAG CPU trace mismatch at cycle {cycle}")
    state := actual.1
  IO.println s!"DAG CPU: {c.nodes.length} nodes, {graph.gates.size} gates, 32 opcode/reset cases and 64 trace steps passed"

#eval main
#print axioms HDLean.Toy16.DagPhysical.hardware_correct
#print axioms HDLean.Toy16.DagPhysical.emit_correct
#print axioms HDLean.Dag.Build.run_implements
#print axioms HDLean.Dag.Build.Word.selectBalanced_ensures

end HDLean.Dag.Build.Tests
