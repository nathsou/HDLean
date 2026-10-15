import HDLean.Backend.Graph
import Std.Data.HashMap

namespace HDLean.Backend

private structure FastBuild (d i r : Nat) where
  gates : Array Gate := #[]
  expressions : Std.HashMap USize (Expr d i r × Lit) := {}
  conjunctions : Std.HashMap (Lit × Lit) Lit := {}

private def fastGate (a b : Lit) : StateM (FastBuild d i r) Lit := do
  if a == 0 || b == 0 then return 0
  if a == 1 then return b
  if b == 1 || a == b then return a
  if a == invert b then return 0
  let key := (max a b, min a b)
  if let some l := (← get).conjunctions[key]? then return l
  let s ← get
  let v := i + 1 + r + s.gates.size + 1
  set { s with
    gates := s.gates.push ⟨v, key.1, key.2⟩
    conjunctions := s.conjunctions.insert key (2 * v) }
  return 2*v

private def fastMux (c a b : Lit) : StateM (FastBuild d i r) Lit := do
  let x ← fastGate c a
  let y ← fastGate (invert c) b
  return invert (← fastGate (invert x) (invert y))

/-- Pointer memoization is confined to untrusted candidate construction. Keeping
an owning expression in each entry prevents address reuse while compiling. -/
private unsafe def fastExpr (e : Expr d i r) : StateM (FastBuild d i r) Lit := do
  let key := ptrAddrUnsafe e
  if let some (_,l) := (← get).expressions[key]? then return l
  let l ← match e with
    | .lit b => pure (if b then 1 else 0)
    | .input k => pure (2*(k.val+1))
    | .reg k => pure (2*(i+2+k.val))
    | .inv a => return invert (← fastExpr a)
    | .and a b => do fastGate (← fastExpr a) (← fastExpr b)
    | .xor a b => do
      let x ← fastExpr a
      let y ← fastExpr b
      let xy ← fastGate x y
      let nn ← fastGate (invert x) (invert y)
      fastGate (invert xy) (invert nn)
    | .mux c a b => do fastMux (← fastExpr c) (← fastExpr a) (← fastExpr b)
  modify fun s => {s with expressions := s.expressions.insert key (e,l)}
  return l

unsafe def fastCompile (c : Circuit d i r o) : Graph := Id.run do
  let job : StateM (FastBuild d i r) (Array Lit × Array Lit) := do
    let mut ns := #[]
    for j in List.finRange r do
      let reg := c.state[j]
      let n ← fastExpr reg.next
      let n ← match reg.reset with
        | .unreset => pure n
        | .hold => fastMux (2*(i+1)) (2*(i+2+j.val)) n
        | .synchronous b => fastMux (2*(i+1)) (if b then 1 else 0) n
      ns := ns.push n
    let mut os := #[]
    for out in c.output.toArray do os := os.push (← fastExpr out)
    return (ns,os)
  let ((ns,os),s) := job.run {}
  return ⟨c.name,i+1,r,s.gates,ns,os,c.inputNames.toArray.push "rst",
    c.state.toArray.map (·.name),c.outputNames.toArray,c.state.toArray.map (·.source)⟩

/-- Native candidate search is optimized independently of the proved validator.
Its logical fallback is the original compiler. Every candidate, including output
from the unsafe pointer cache, must pass semantic validation before emission. -/
@[implemented_by fastCompile]
def compileCandidate (c : Circuit d i r o) : Graph := compile (lower c)

end HDLean.Backend
