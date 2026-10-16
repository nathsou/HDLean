import HDLean.Core.Circuit

namespace HDLean
namespace Dag

/-- Node references name earlier results in this domain's local node list.
Inputs and registers are bounded local ports, never global state indices. -/
inductive Op (d : Domain) (inputs regs : Nat) where
  | lit (value : Bool)
  | input (index : Fin inputs)
  | reg (index : Fin regs)
  | not (arg : Nat)
  | and (left right : Nat)
  | xor (left right : Nat)
  | mux (sel yes no : Nat)
  deriving Repr, BEq, DecidableEq

/-- Every combinational dependency strictly precedes its consumer. -/
def Op.Valid (bound : Nat) : Op d i r → Prop
  | .lit _ | .input _ | .reg _ => True
  | .not a => a < bound
  | .and a b | .xor a b => a < bound ∧ b < bound
  | .mux s a b => s < bound ∧ a < bound ∧ b < bound

instance (bound : Nat) (op : Op d i r) : Decidable (op.Valid bound) := by
  cases op <;> unfold Op.Valid <;> infer_instance

def NodesWF : Nat → List (Op d i r) → Prop
  | _, [] => True
  | k, op :: rest => op.Valid k ∧ NodesWF (k+1) rest

def nodesWFDecidable (k : Nat) (ops : List (Op d i r)) : Decidable (NodesWF k ops) :=
  match ops with
  | [] => isTrue trivial
  | op :: rest => @instDecidableAnd _ _ (inferInstance : Decidable (op.Valid k))
      (nodesWFDecidable (k+1) rest)
instance (k : Nat) (ops : List (Op d i r)) : Decidable (NodesWF k ops) := nodesWFDecidable k ops

@[simp] theorem nodesWF_nil : NodesWF k ([] : List (Op d i r)) := trivial
@[simp] theorem nodesWF_cons : NodesWF k (op :: ops) ↔ op.Valid k ∧ NodesWF (k+1) ops := Iff.rfl

theorem nodesWF_append (xs ys : List (Op d i r)) (k : Nat) :
    NodesWF k (xs ++ ys) ↔ NodesWF k xs ∧ NodesWF (k + xs.length) ys := by
  induction xs generalizing k with
  | nil => simp [NodesWF]
  | cons x xs ih =>
    simp only [List.cons_append, NodesWF, ih, List.length_cons]
    rw [show k + 1 + xs.length = k + (xs.length + 1) by omega]
    exact and_assoc.symm

theorem nodesWF_snoc {ops : List (Op d i r)} (h : NodesWF 0 ops) (hop : (op : Op d i r).Valid ops.length) :
    NodesWF 0 (ops ++ [op]) := by
  rw [nodesWF_append]
  exact ⟨h, by simpa [NodesWF] using hop⟩

def WellFormed (nodes : List (Op d i r)) (next : Vector Nat r) (out : Vector Nat o) : Prop :=
  NodesWF 0 nodes ∧ (∀ k : Fin r, next[k] < nodes.length) ∧
    (∀ k : Fin o, out[k] < nodes.length)

instance (nodes : List (Op d i r)) (next : Vector Nat r) (out : Vector Nat o) :
    Decidable (WellFormed nodes next out) := by unfold WellFormed; infer_instance

def Op.eval (xs : Fin i → Bool) (s : Fin r → Bool) (values : Nat → Bool) : Op d i r → Bool
  | .lit b => b
  | .input k => xs k
  | .reg k => s k
  | .not a => !(values a)
  | .and a b => values a && values b
  | .xor a b => Bool.xor (values a) (values b)
  | .mux c a b => if values c then values a else values b

def read (values : Array Bool) (k : Nat) : Bool := values[k]?.getD false

/-- Each node is evaluated once and appended; references read previously stored values. -/
def evalNodes (nodes : List (Op d i r)) (xs : Fin i → Bool) (s : Fin r → Bool)
    (initial : Array Bool := #[]) : Array Bool :=
  nodes.foldl (fun values op => values.push (op.eval xs s (read values))) initial

@[simp] theorem evalNodes_size (nodes : List (Op d i r)) (xs s initial) :
    (evalNodes nodes xs s initial).size = initial.size + nodes.length := by
  induction nodes generalizing initial with
  | nil => simp [evalNodes]
  | cons op nodes ih =>
    change (evalNodes nodes xs s (initial.push (op.eval xs s (read initial)))).size = _
    rw [ih]
    simp only [Array.size_push, List.length_cons]
    omega

def resetValue (kind : ResetKind) (old value rst : Bool) : Bool :=
  match kind with
  | .unreset => value
  | .hold => if rst then old else value
  | .synchronous b => if rst then b else value

end Dag

/-- A finite, explicitly shared single-domain circuit. Different domains have
separate local input/register spaces; no operation can read a foreign space. -/
structure Dag (d : Domain) (inputs regs outputs : Nat) where
  name : String
  nodes : List (Dag.Op d inputs regs)
  next : Vector Nat regs
  out : Vector Nat outputs
  reset : Vector ResetKind regs
  wf : Dag.WellFormed nodes next out
  inputNames : Vector String inputs := Vector.ofFn fun k => s!"in_{k.val}"
  stateNames : Vector String regs := Vector.ofFn fun k => s!"state_{k.val}"
  outputNames : Vector String outputs := Vector.ofFn fun k => s!"out_{k.val}"
  sources : Vector String regs := Vector.replicate regs ""

namespace Dag

def values (c : Dag d i r o) (xs : Fin i → Bool) (s : Fin r → Bool) : Array Bool :=
  evalNodes c.nodes xs s

def nextState (c : Dag d i r o) (s : Fin r → Bool) (xs : (Fin i → Bool) × Bool) : Fin r → Bool :=
  let v := c.values xs.1 s
  fun k => resetValue c.reset[k] (s k) (read v c.next[k]) xs.2

def evalOutput (c : Dag d i r o) (s : Fin r → Bool) (xs : Fin i → Bool) : Fin o → Bool :=
  let v := c.values xs s
  fun k => read v c.out[k]

def step (c : Dag d i r o) (s : Fin r → Bool) (xs : (Fin i → Bool) × Bool) :
    (Fin r → Bool) × (Fin o → Bool) := (c.nextState s xs, c.evalOutput s xs.1)

/-- Physical state bits; fixed by the graph's type. -/
def ffBits (_ : Dag d i r o) : Nat := r

/-- Outputs do not depend on current inputs. -/
def IsMoore (c : Dag d i r o) : Prop :=
  ∀ s a b, c.evalOutput s a = c.evalOutput s b

/-- Hardware semantics: power-up state is an argument, inputs are (data, reset). -/
def denote (c : Dag d i r o) (_moore : c.IsMoore) :
    PMachine (Fin r → Bool) ((Fin i → Bool) × Bool) (Fin o → Bool) :=
  ⟨fun s => c.evalOutput s (fun _ => false), c.nextState⟩

/-- A graph with no inputs is Moore. -/
theorem isMoore_of_no_inputs (c : Dag d 0 r o) : c.IsMoore := by
  intro s a b
  have : a = b := funext fun k => k.elim0
  rw [this]

@[simp] theorem values_size (c : Dag d i r o) (xs s) : (c.values xs s).size = c.nodes.length := by
  simp [values]

end Dag
end HDLean
