import HDLean.Netlist.DagLower

namespace HDLean.Dag.Tests

def exampleDag : Dag 0 1 3 4 where
  name := "dag-reset-and-sharing"
  nodes := [.input ⟨0,by decide⟩, .reg ⟨0,by decide⟩, .lit true,
    .not 0, .and 0 1, .xor 0 1, .mux 0 2 1, .and 5 5]
  next := #v[3,5,6]
  out := #v[4,5,6,7]
  reset := #v[.unreset,.hold,.synchronous false]
  wf := by decide

example : exampleDag.lower.gates.size = 33 := by decide
example : exampleDag.lower.wellFormed = true := lower_wellFormed exampleDag

-- Arbitrary initial state and both reset phases are covered by the generic theorem.
example (xs : Vector Bool 1) (s : Vector Bool 3) (rst : Bool) :
    exampleDag.lower.eval (xs.toArray.push rst) s.toArray =
      ((Vector.ofFn (exampleDag.nextState (fun k => s[k]) ((fun k => xs[k]),rst))).toArray,
       (Vector.ofFn (exampleDag.evalOutput (fun k => s[k]) (fun k => xs[k]))).toArray) :=
  lower_correct exampleDag xs s rst

example : exampleDag.lower.eval #[true,true] #[false,true,true] =
    (#[false,true,false], #[false,true,true,true]) := by decide +kernel
example : exampleDag.lower.eval #[false,false] #[true,false,false] =
    (#[true,true,true], #[false,true,true,true]) := by decide +kernel

-- A forward/self reference cannot enter the trusted DAG representation.
example : ¬ NodesWF 0 ([.not 0] : List (Op 0 1 1)) := by decide +kernel
example : NodesWF 0 ([.lit true,.and 0 0,.xor 1 1] : List (Op 0 0 0)) := by decide +kernel

#print axioms HDLean.Dag.lower_correct
#print axioms HDLean.Dag.lower_wellFormed
end HDLean.Dag.Tests
