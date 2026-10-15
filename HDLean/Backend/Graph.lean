import HDLean.Netlist.Lower
namespace HDLean.Backend

/-- AIGER literal: variable index in the high bits, inversion in the low bit. -/
abbrev Lit := Nat
structure Gate where
  lhs : Nat
  a : Lit
  b : Lit
  deriving Repr, BEq

/-- A topologically ordered shared AIG, with explicit arbitrary initial latch values. -/
structure Graph where
  name : String
  inputs : Nat
  latches : Nat
  gates : Array Gate
  next : Array Lit
  outputs : Array Lit
  inputNames : Array String
  stateNames : Array String
  outputNames : Array String
  sources : Array String
  deriving Repr

private structure Build (d i r : Nat) where
  gates : Array Gate := #[]
  cache : Std.HashMap (Netlist.Node d i r) Lit := {}

def invert (a : Lit) : Lit := a ^^^ 1

private def gate (a b : Lit) : StateM (Build d i r) Lit := do
  if a == 0 || b == 0 then return 0
  if a == 1 then return b
  if b == 1 || a == b then return a
  if a == invert b then return 0
  let s ← get
  let v := i + 1 + r + s.gates.size + 1
  set { s with gates := s.gates.push ⟨v, max a b, min a b⟩ }
  return 2 * v

private def compileNode (n : Netlist.Node d i r) : StateM (Build d i r) Lit := do
  if let some l := (← get).cache[n]? then return l
  let l ← match n with
    | .lit b => pure (if b then 1 else 0)
    | .input k => pure (2 * (k.val + 1))
    | .reg k => pure (2 * (i + 1 + k.val + 1))
    | .inv a => return invert (← compileNode a)
    | .and a b => do
      let a ← compileNode a
      let b ← compileNode b
      gate a b
  modify fun s => { s with cache := s.cache.insert n l }
  return l

private def muxLit (c a b : Lit) : StateM (Build d i r) Lit := do
  let ca ← gate c a
  let nb ← gate (invert c) b
  return invert (← gate (invert ca) (invert nb))

/-- Sharing and numbering are untrusted until checked by `Graph.Equivalent`. -/
def compile (m : Netlist.Module d i r o) : Graph := Id.run do
  let job : StateM (Build d i r) (Array Lit × Array Lit) := do
    let mut ns := #[]
    for reg in m.state.toArray do
      let n ← compileNode reg.next
      let n ← match reg.reset with
        | .unreset => pure n
        | .synchronous b => muxLit (2 * (i + 1)) (if b then 1 else 0) n
      ns := ns.push n
    let mut os := #[]
    for out in m.output.toArray do os := os.push (← compileNode out)
    return (ns, os)
  let ((ns, os), s) := job.run {}
  return ⟨m.name, i + 1, r, s.gates, ns, os,
    m.inputNames.toArray.push "rst", m.state.toArray.map (·.name),
    m.outputNames.toArray, m.state.toArray.map (·.source)⟩

def litValue (values : Array Bool) (l : Lit) : Bool :=
  xor (values[l / 2]?.getD false) (l % 2 == 1)

def Graph.values (g : Graph) (inputs state : Array Bool) : Array Bool := Id.run do
  let mut values := #[false] ++ inputs ++ state
  for gate in g.gates do
    values := values.push (litValue values gate.a && litValue values gate.b)
  return values

def Graph.eval (g : Graph) (inputs state : Array Bool) : Array Bool × Array Bool :=
  let v := g.values inputs state
  (g.next.map (litValue v), g.outputs.map (litValue v))

/-- Reject dangling, forward, cyclic, malformed or dimensionally inconsistent graphs. -/
def Graph.wellFormed (g : Graph) : Bool := Id.run do
  if g.inputs == 0 || g.next.size != g.latches then return false
  if g.inputNames.size != g.inputs || g.stateNames.size != g.latches ||
      g.sources.size != g.latches || g.outputNames.size != g.outputs.size then return false
  let mut v := g.inputs + g.latches + 1
  for gate in g.gates do
    if gate.lhs != v || gate.a / 2 ≥ v || gate.b / 2 ≥ v then return false
    v := v + 1
  return g.next.all (fun l => l / 2 < v) && g.outputs.all (fun l => l / 2 < v)

/-- A certificate ties a shared graph to the exact circuit for every state, input and reset. -/
def Graph.Equivalent (g : Graph) (c : Circuit d i r o) : Prop :=
  g.wellFormed = true ∧ g.inputs = i + 1 ∧ g.latches = r ∧ g.outputs.size = o ∧
  ∀ (xs : Vector Bool i) (s : Vector Bool r) (rst : Bool),
    g.eval (xs.toArray.push rst) s.toArray =
      ((Vector.ofFn (c.next (fun k => s[k]) ((fun k => xs[k]), rst))).toArray,
       (Vector.ofFn (c.evalOutput (fun k => s[k]) (fun k => xs[k]))).toArray)

/-- Exact shared-graph metrics; includes reset logic, unlike the pre-sharing tree estimate. -/
def Graph.andCount (g : Graph) := g.gates.size
def Graph.ffBits (g : Graph) := g.latches
def Graph.depth (g : Graph) : Nat := Id.run do
  let mut depths := Array.replicate (g.inputs + g.latches + 1) 0
  for gate in g.gates do
    depths := depths.push (max (depths[gate.a / 2]?.getD 0) (depths[gate.b / 2]?.getD 0) + 1)
  return (g.next ++ g.outputs).foldl (fun m l => max m (depths[l / 2]?.getD 0)) 0
end HDLean.Backend
