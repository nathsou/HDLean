import HDLean.Core.DagBuilder

namespace HDLean.Dag.Allocate

/-- A register handle is allocated by the builder; user code never computes a
physical offset. Its node reads that register's pre-edge value. -/
structure Register (r : Nat) where
  index : Fin r
  value : Build.Ref

structure State (d : Domain) (i r : Nat) where
  graph : Build.State d i r
  available : List (Fin r)
  reset : Vector ResetKind r
  drivers : Vector (Option Build.Ref) r

abbrev M (d : Domain) (i r : Nat) := StateT (State d i r) Option

def empty : State d i r :=
  ⟨Build.empty,List.finRange r,Vector.replicate r .unreset,Vector.replicate r none⟩

/-- Lift a node-allocating operation without changing the register allocator. -/
def node (action : Build.M d i r α) : M d i r α := fun s => do
  let (a,g) ← action s.graph
  pure (a,{s with graph := g})

def literal (b : Bool) : M d i r Build.Ref := node (Build.literal b)
def input (k : Fin i) : M d i r Build.Ref := node (Build.input k)
def inv (a : Build.Ref) : M d i r Build.Ref := node (Build.inv a)
def and (a b : Build.Ref) : M d i r Build.Ref := node (Build.and a b)
def xor (a b : Build.Ref) : M d i r Build.Ref := node (Build.xor a b)
def mux (c a b : Build.Ref) : M d i r Build.Ref := node (Build.mux c a b)

def register (reset : ResetKind) : M d i r (Register r) := fun s => do
  let k::remaining := s.available | none
  let (ref,g) ← Build.reg k s.graph
  pure (⟨k,ref⟩,{s with graph := g, available := remaining, reset := s.reset.set k reset})

/-- Synchronously reset storage. Reset never changes the number of allocated bits. -/
def regR (initial : Bool := false) : M d i r (Register r) := register (.synchronous initial)

/-- Unreset storage, universally quantified at power-up by circuit semantics. -/
def regN : M d i r (Register r) := register .unreset

/-- Every allocated register must have exactly one next-state driver. -/
def drive (reg : Register r) (next : Build.Ref) : M d i r Unit := fun s =>
  if s.available.contains reg.index || s.drivers[reg.index].isSome then none
  else some ((),{s with drivers := s.drivers.set reg.index (some next)})

/-- Word banks allocate consecutive handles without exposing any offsets. -/
abbrev WordRegister (r w : Nat) := Vector (Register r) w

def WordRegister.value (word : WordRegister r w) : Build.Word w := word.map Register.value

def regRWord (w : Nat) (initial : Bool := false) : M d i r (WordRegister r w) :=
  (Vector.replicate w ()).mapM (fun _ => regR initial)

def regNWord (w : Nat) : M d i r (WordRegister r w) :=
  (Vector.replicate w ()).mapM (fun _ => regN)

def driveWord (word : WordRegister r w) (next : Build.Word w) : M d i r Unit := do
  let _ ← (Vector.ofFn fun k : Fin w => k).mapM (fun k => drive word[k] next[k])
  pure ()

/-- Finalization only checks structural references and complete single drivers.
It neither translates expressions nor compares source and target semantics. -/
def finish (name : String) (outputs : Vector Build.Ref o) (s : State d i r) : Option (Dag d i r o) :=
  if s.available.isEmpty then
    if h : ∀ k : Fin r, s.drivers[k].isSome then
      Build.finish name (Vector.ofFn fun k => s.drivers[k].get (h k)) outputs s.reset s.graph
    else none
  else none

def run (name : String) (program : M d i r (Vector Build.Ref o)) : Option (Dag d i r o) := do
  let (outputs,s) ← program empty
  finish name outputs s

/-- Successful driving records exactly the requested next-state node. -/
theorem drive_records (reg : Register r) (next : Build.Ref) (s t : State d i r)
    (h : drive reg next s = some ((),t)) : t.drivers[reg.index] = some next := by
  simp only [drive] at h
  split at h
  · contradiction
  · cases h
    simp

/-- Node allocation has exactly the same structural validity check as the shared core. -/
theorem node_graph (action : Build.M d i r α) (s t : State d i r) (a : α)
    (h : node action s = some (a,t)) : action s.graph = some (a,t.graph) := by
  unfold node at h
  cases he : action s.graph with
  | none => simp [he] at h
  | some p =>
    rcases p with ⟨b,g⟩
    simp [he] at h
    rcases h with ⟨rfl,rfl⟩
    rfl

end HDLean.Dag.Allocate
