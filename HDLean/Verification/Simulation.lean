import HDLean.Core.TreeToDag
import HDLean.Netlist.DagLower
namespace HDLean.Verification

/-- Reproducible PRNG, independent of platform random-number implementations. -/
def random (seed : Nat) : Nat := (1664525 * seed + 1013904223) % 4294967296

def randomBits (n seed : Nat) : Array Bool × Nat := Id.run do
  let mut seed := seed
  let mut bits := #[]
  for _ in [:n] do
    seed := random seed
    bits := bits.push (seed / 65536 % 2 == 1)
  return (bits, seed)

def bitsToNat (bits : Array Bool) : Nat :=
  (bits.toList.zipIdx).foldl (fun n (b, k) => if b then n + 2 ^ k else n) 0

def natToBits (n value : Nat) : Array Bool := (List.range n).toArray.map (fun k => value / 2 ^ k % 2 == 1)

/-- Compare a reference step function with a gate graph on arbitrary state,
including during reset. The proofs already cover this for every circuit; the check
guards the compiled code that computes and evaluates the graph. -/
def checkStep (graph : Backend.Graph) (i r o : Nat)
    (step : (Fin r → Bool) → (Fin i → Bool) → Bool → Array Bool × Array Bool)
    (cycles seed : Nat) : Except String Unit := do
  unless graph.wellFormed do throw "malformed gate graph"
  let (initial, seed) := randomBits r seed
  let mut state := initial
  let mut seed := seed
  for t in [:cycles] do
    let (input, seed') := randomBits i seed
    seed := seed'
    let rst := t == 0 || t % 19 == 0
    let (next, out) := step (fun k => state[k.val]!) (fun k => input[k.val]!) rst
    let actual := graph.eval (input.push rst) state
    if actual != (next, out) then
      let mut signals := #[]
      for k in [:r] do
        if next[k]! != actual.1[k]! then
          signals := signals.push s!"state {graph.stateNames[k]!} at {graph.sources[k]!}: expected {next[k]!}, actual {actual.1[k]!}"
      for k in [:o] do
        if out[k]! != actual.2[k]! then
          signals := signals.push s!"output {graph.outputNames[k]!}: expected {out[k]!}, actual {actual.2[k]!}"
      throw s!"cycle {t}: reference/graph mismatch; {String.intercalate "; " signals.toList}; input={input}, state={state}"
    state := next

/-- A tree circuit against its emitted gate graph. -/
def checkCircuit (c : Circuit d i r o) (cycles seed : Nat) : Except String Unit :=
  checkStep c.toDag.lower i r o (fun s xs rst =>
    ((Vector.ofFn (c.next s (xs, rst))).toArray, (Vector.ofFn (c.evalOutput s xs)).toArray)) cycles seed

/-- A node graph against its emitted gate graph. -/
def checkDag (c : Dag d i r o) (cycles seed : Nat) : Except String Unit :=
  checkStep c.lower i r o (fun s xs rst =>
    ((Vector.ofFn (c.nextState s (xs, rst))).toArray, (Vector.ofFn (c.evalOutput s xs)).toArray)) cycles seed

/-- A trace row exposes pre-edge outputs and post-edge state, avoiding cycle ambiguity. -/
structure TraceRow where
  cycle : Nat
  inputs : Array Bool
  state : Array Bool
  outputs : Array Bool
  next : Array Bool
  deriving Repr

def trace (g : Backend.Graph) (cycles seed : Nat) : Array TraceRow := Id.run do
  let (initial, seed) := randomBits g.latches seed
  let mut state := initial
  let mut seed := seed
  let mut rows := #[]
  for t in [:cycles] do
    let (input, seed') := randomBits (g.inputs - 1) seed
    seed := seed'
    let input := input.push (t == 0 || t % 19 == 0)
    let (next, out) := g.eval input state
    rows := rows.push ⟨t, input, state, out, next⟩
    state := next
  return rows
end HDLean.Verification
