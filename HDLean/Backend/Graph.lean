import HDLean.Core.Circuit
namespace HDLean.Backend

/-- AIGER literal: variable index in the high bits, inversion in the low bit. -/
abbrev Lit := Nat
structure Gate where
  lhs : Nat
  a : Lit
  b : Lit
  deriving Repr, BEq, DecidableEq

/-- A topologically ordered AND-inverter graph, the target of `Dag.lower`.
Latches have no initial value: power-up contents are arbitrary. -/
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

def litValue (values : Array Bool) (l : Lit) : Bool :=
  xor (values[l / 2]?.getD false) (l % 2 == 1)

def Graph.values (g : Graph) (inputs state : Array Bool) : Array Bool :=
  g.gates.foldl (fun values gate =>
    values.push (litValue values gate.a && litValue values gate.b)) (#[false] ++ inputs ++ state)

def Graph.eval (g : Graph) (inputs state : Array Bool) : Array Bool × Array Bool :=
  let v := g.values inputs state
  (g.next.map (litValue v), g.outputs.map (litValue v))

/-- Reject dangling, forward, cyclic, malformed or dimensionally inconsistent graphs. -/
def Graph.wellFormed (g : Graph) : Bool := Id.run do
  if g.inputs == 0 || g.next.size != g.latches then return false
  if g.inputNames.size != g.inputs || g.stateNames.size != g.latches ||
      g.sources.size != g.latches || g.outputNames.size != g.outputs.size then return false
  let mut v := g.inputs + g.latches + 1
  -- List traversal also reduces linearly in the logical Array representation.
  for gate in g.gates.toList do
    if gate.lhs != v || gate.a / 2 ≥ v || gate.b / 2 ≥ v then return false
    v := v + 1
  return g.next.toList.all (fun l => l / 2 < v) && g.outputs.toList.all (fun l => l / 2 < v)

deriving instance ReflBEq, LawfulBEq for Gate

/-- The semantic part of a module; names and source annotations are metadata. -/
structure Logic where
  inputs : Nat
  latches : Nat
  gates : Array Gate
  next : Array Lit
  outputs : Array Lit
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def Graph.logic (g : Graph) : Logic := ⟨g.inputs, g.latches, g.gates, g.next, g.outputs⟩

theorem Graph.eval_eq_of_logic_eq (a b : Graph) (h : a.logic = b.logic) (inputs state) :
    a.eval inputs state = b.eval inputs state := by
  cases a
  cases b
  simp only [Graph.logic, Logic.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

/-- Exact shared-graph metrics; includes reset logic, unlike the pre-sharing tree estimate. -/
def Graph.andCount (g : Graph) := g.gates.size
def Graph.ffBits (g : Graph) := g.latches
def Graph.depth (g : Graph) : Nat := Id.run do
  let mut depths := Array.replicate (g.inputs + g.latches + 1) 0
  for gate in g.gates do
    depths := depths.push (max (depths[gate.a / 2]?.getD 0) (depths[gate.b / 2]?.getD 0) + 1)
  return (g.next ++ g.outputs).foldl (fun m l => max m (depths[l / 2]?.getD 0)) 0
end HDLean.Backend
