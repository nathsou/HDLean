import HDLean.Backend.FastCompile
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

/-- Compare the executable AST with the shared IR on arbitrary state, including during reset. -/
def checkCircuit (c : Circuit d i r o) (cycles seed : Nat) : Except String Unit := do
  let graph := Backend.compileCandidate c
  unless graph.wellFormed do throw "malformed shared graph"
  let (initial, seed) := randomBits r seed
  let mut state := initial
  let mut seed := seed
  for t in [:cycles] do
    let (input, seed') := randomBits i seed
    seed := seed'
    let rst := t == 0 || t % 19 == 0
    let s : Fin r → Bool := fun k => state[k.val]!
    let xs : Fin i → Bool := fun k => input[k.val]!
    let next := (Vector.ofFn (c.next s (xs, rst))).toArray
    let out := (Vector.ofFn (c.evalOutput s xs)).toArray
    let actual := graph.eval (input.push rst) state
    if actual != (next, out) then
      throw s!"cycle {t}: AST/graph mismatch; input={input}, state={state}, expected={(next,out)}, actual={actual}"
    state := next

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
