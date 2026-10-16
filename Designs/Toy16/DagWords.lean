import HDLean.Core.DagBuilderBlock

namespace HDLean.Dag.Build.Word

def literal (v : BitVec w) : M d i r (Word w) := emitWord fun k => .lit (v.getLsbD k.val)
def registers (off : Nat) (h : off+w ≤ r) : M d i r (Word w) :=
  emitWord fun k => .reg ⟨off+k.val,by omega⟩
def mux (c : Ref) (a b : Word w) : M d i r (Word w) := emitWord fun k => .mux c a[k] b[k]
def bitAnd (a b : Word w) : M d i r (Word w) := tabulate fun k => Build.and a[k] b[k]
def bitOr (a b : Word w) : M d i r (Word w) := tabulate fun k => Build.or a[k] b[k]
def bitXor (a b : Word w) : M d i r (Word w) := tabulate fun k => Build.xor a[k] b[k]
def bitNot (a : Word w) : M d i r (Word w) := tabulate fun k => Build.inv a[k]
def extract (a : Word w) (off len : Nat) (h : off+len ≤ w) : Word len :=
  Vector.ofFn fun k => a[off+k.val]'(by omega)
def setWidth (zero : Ref) (a : Word w) (size : Nat) : Word size :=
  Vector.ofFn fun k => if h : k.val < w then a[k.val] else zero
def signExtend (zero : Ref) (a : Word w) (size : Nat) : Word size :=
  Vector.ofFn fun k => if h : k.val < w then a[k.val]
    else if h : 0 < w then a[w-1]'(by omega) else zero

/-- The carry is allocated once per bit and reused by sum and next-carry logic. -/
def addAux (a b : Word w) (initial : Ref) : (n : Nat) → n ≤ w → M d i r (Word n × Ref)
  | 0, _ => pure (#v[],initial)
  | n+1, h => do
    let (bits,carry) ← addAux a b initial n (by omega)
    let x ← Build.xor a[n] b[n]
    let sum ← Build.xor x carry
    let carry ← Build.or (← Build.and a[n] b[n]) (← Build.and x carry)
    pure (bits.push sum,carry)

def add (zero : Ref) (a b : Word w) : M d i r (Word w) := do
  pure (← addAux a b zero w (Nat.le_refl w)).1
def sub (one : Ref) (a b : Word w) : M d i r (Word w) := do
  let nb ← bitNot b
  pure (← addAux a nb one w (Nat.le_refl w)).1
def ult (one : Ref) (a b : Word w) : M d i r Ref := do
  let nb ← bitNot b
  Build.inv (← addAux a nb one w (Nat.le_refl w)).2

def equalAux (a b : Word w) (one : Ref) : (n : Nat) → n ≤ w → M d i r Ref
  | 0, _ => pure one
  | n+1, h => do
    let previous ← equalAux a b one n (by omega)
    Build.and previous (← Build.inv (← Build.xor a[n] b[n]))
def equal (one : Ref) (a b : Word w) : M d i r Ref := equalAux a b one w (Nat.le_refl w)

/-- Balanced physical read tree. The selected address wires are shared at every branch. -/
def selectBalanced : {a : Nat} → Word a → (Fin (2^a) → Word w) → M d i r (Word w)
  | 0, _, table => pure (table ⟨0,by decide⟩)
  | a+1, address, table => do
    let low := extract address 0 a (by omega)
    let yes ← selectBalanced low fun j => table ⟨2^a+j.val, by
      have := j.isLt; simp only [Nat.pow_succ,Nat.mul_two]; omega⟩
    let no ← selectBalanced low fun j => table ⟨j.val, by
      have := j.isLt; simp only [Nat.pow_succ,Nat.mul_two]; omega⟩
    mux address[a] yes no

end HDLean.Dag.Build.Word
