import HDLean.Backend.Graph
namespace HDLean.Backend
private def btorLit (l : Lit) : Nat := if l < 2 then l + 2 else 2 * (l / 2) + 2 + l % 2

/-- BTOR2 Boolean transition system; absent init statements mean arbitrary power-up. -/
def btor2 (g : Graph) : String := Id.run do
  let mut lines := #["1 sort bitvec 1", "2 zero 1", "3 one 1"]
  for k in [:g.inputs] do
    let id := 2 * (k + 1) + 2
    lines := lines.push s!"{id} input 1 in_{k}"
    lines := lines.push s!"{id + 1} not 1 {id}"
  for k in [:g.latches] do
    let id := 2 * (g.inputs + k + 1) + 2
    lines := lines.push s!"{id} state 1 reg_{k}"
    lines := lines.push s!"{id + 1} not 1 {id}"
  for gate in g.gates do
    let id := 2 * gate.lhs + 2
    lines := lines.push s!"{id} and 1 {btorLit gate.a} {btorLit gate.b}"
    lines := lines.push s!"{id + 1} not 1 {id}"
  let mut id := 2 * (g.inputs + g.latches + g.gates.size + 1) + 2
  for k in [:g.latches] do
    lines := lines.push s!"{id} next 1 {2 * (g.inputs + k + 1) + 2} {btorLit g.next[k]!}"
    id := id + 1
  for k in [:g.outputs.size] do
    lines := lines.push s!"{id} output {btorLit g.outputs[k]!} out_{k}"
    id := id + 1
  return String.intercalate "\n" lines.toList ++ "\n"
end HDLean.Backend
