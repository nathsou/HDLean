import HDLean.Core.DagBuilderBlock

namespace HDLean.Dag.Build.BlockTests

-- A block cannot smuggle an intra-block forward reference past the boundary.
example : emitBlock (fun k : Fin 2 => if k.val = 0 then .lit true else .not 0)
    (empty : State 0 0 0) = none := by decide +kernel

-- Independent nodes receive consecutive references and preserve their order.
def sample : M 0 1 0 (Word 3) := do
  let a ← input ⟨0, by decide⟩
  emitWord fun k => if k.val = 0 then .not a else .xor a a

example : (sample empty).map (fun (refs,s) => (refs,s.count,s.reversed.reverse)) =
    some (#v[1,2,3],4,[.input ⟨0,by decide⟩,.not 0,.xor 0 0,.xor 0 0]) := by decide +kernel

example (s : State 0 1 0) :
    Ensures s (emitWord fun _ : Fin 0 => .lit true)
      (fun refs t => WordRefines t refs (Vector.ofFn fun _ => .lit true)) := by
  simpa [WordRefines] using emitWord_ensures s (fun _ : Fin 0 => .lit true) (fun _ => trivial)

#print axioms HDLean.Dag.Build.emitWord_ensures

end HDLean.Dag.Build.BlockTests
