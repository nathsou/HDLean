import HDLean.Core.Expr
namespace HDLean

/-- Reset is attached to every state element, including explicit non-resettable storage. -/
inductive ResetKind where
  | unreset
  | hold
  | synchronous (value : Bool)
  deriving Repr, BEq

structure Register (d i r : Nat) where
  name : String
  reset : ResetKind
  next : Expr d i r
  source : String := ""

/-- Finite netlists have exactly one driver for each register and output. -/
structure Circuit (d inputs regs outputs : Nat) where
  name : String
  state : Vector (Register d inputs regs) regs
  output : Vector (Expr d inputs regs) outputs
  inputNames : Vector String inputs := Vector.ofFn fun k => s!"in_{k.val}"
  outputNames : Vector String outputs := Vector.ofFn fun k => s!"out_{k.val}"

namespace Circuit

def next (c : Circuit d i r o) (s : Fin r → Bool) (xs : (Fin i → Bool) × Bool) : Fin r → Bool :=
  fun k => match c.state[k].reset with
    | .unreset => c.state[k].next.eval xs.1 s
    | .hold => if xs.2 then s k else c.state[k].next.eval xs.1 s
    | .synchronous v => if xs.2 then v else c.state[k].next.eval xs.1 s

def evalOutput (c : Circuit d i r o) (s : Fin r → Bool) (xs : Fin i → Bool) : Fin o → Bool :=
  fun k => c.output[k].eval xs s

/-- Mealy observation is explicit; the state transition still samples only old state. -/
def step (c : Circuit d i r o) (s : Fin r → Bool) (xs : (Fin i → Bool) × Bool) :
    (Fin r → Bool) × (Fin o → Bool) := (c.next s xs, c.evalOutput s xs.1)

/-- Physical state bits; fixed by the circuit's type. -/
def ffBits (_ : Circuit d i r o) : Nat := r

/-- Moore restriction is a proof, not an unchecked label on a port. -/
def IsMoore (c : Circuit d i r o) : Prop :=
  ∀ s a b, c.evalOutput s a = c.evalOutput s b

def denote (c : Circuit d i r o) (_moore : c.IsMoore) : PMachine (Fin r → Bool) ((Fin i → Bool) × Bool) (Fin o → Bool) :=
  ⟨fun s => c.evalOutput s (fun _ => false), c.next⟩

end Circuit

end HDLean
