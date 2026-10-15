import HDLean.Core.Circuit
namespace HDLean.Netlist

/-- AND/inverter IR. Domain identities remain static through lowering. -/
inductive Node (d i r : Nat) where
  | lit (b : Bool)
  | input (k : Fin i)
  | reg (k : Fin r)
  | inv (a : Node d i r)
  | and (a b : Node d i r)
  deriving Repr, BEq, Hashable

def Node.eval (xs : Fin i → Bool) (s : Fin r → Bool) : Node d i r → Bool
  | .lit b => b
  | .input k => xs k
  | .reg k => s k
  | .inv a => !(a.eval xs s)
  | .and a b => a.eval xs s && b.eval xs s

def Node.andCount : Node d i r → Nat
  | .and a b => a.andCount + b.andCount + 1
  | .inv a => a.andCount
  | _ => 0

def Node.depth : Node d i r → Nat
  | .and a b => max a.depth b.depth + 1
  | .inv a => a.depth
  | _ => 0

structure Register (d i r : Nat) where
  name : String
  reset : ResetKind
  next : Node d i r
  source : String

structure Module (d i r o : Nat) where
  name : String
  state : Vector (Register d i r) r
  output : Vector (Node d i r) o
  inputNames : Vector String i
  outputNames : Vector String o

def Module.ffBits (_ : Module d i r o) := r
def Module.andCount (m : Module d i r o) :=
  m.state.foldl (fun n x => n + x.next.andCount) 0 + m.output.foldl (fun n x => n + x.andCount) 0
def Module.depth (m : Module d i r o) :=
  max (m.state.foldl (fun n x => max n x.next.depth) 0) (m.output.foldl (fun n x => max n x.depth) 0)
def Module.next (m : Module d i r o) (s : Fin r → Bool) (xs : (Fin i → Bool) × Bool) : Fin r → Bool :=
  fun k => match m.state[k].reset with
    | .unreset => m.state[k].next.eval xs.1 s
    | .hold => if xs.2 then s k else m.state[k].next.eval xs.1 s
    | .synchronous v => if xs.2 then v else m.state[k].next.eval xs.1 s
def Module.evalOutput (m : Module d i r o) (s : Fin r → Bool) (xs : Fin i → Bool) : Fin o → Bool :=
  fun k => m.output[k].eval xs s
end HDLean.Netlist
