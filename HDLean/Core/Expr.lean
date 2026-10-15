import HDLean.Semantics.Machine
namespace HDLean

/-- A clock domain is a static identity, never a runtime signal. -/
abbrev Domain := Nat

/-- Intrinsically bounded, single-domain Boolean expressions. Feedback reads old state only. -/
inductive Expr (d : Domain) (inputs regs : Nat) where
  | lit (value : Bool)
  | input (index : Fin inputs)
  | reg (index : Fin regs)
  | inv (a : Expr d inputs regs)
  | and (a b : Expr d inputs regs)
  | xor (a b : Expr d inputs regs)
  | mux (sel yes no : Expr d inputs regs)
  deriving Repr, BEq, Hashable

namespace Expr

def eval (xs : Fin i → Bool) (s : Fin r → Bool) : Expr d i r → Bool
  | .lit b => b
  | .input k => xs k
  | .reg k => s k
  | .inv a => !(eval xs s a)
  | .and a b => eval xs s a && eval xs s b
  | .xor a b => Bool.xor (eval xs s a) (eval xs s b)
  | .mux c a b => if eval xs s c then eval xs s a else eval xs s b

def or (a b : Expr d i r) : Expr d i r := .inv (.and (.inv a) (.inv b))
instance : Complement (Expr d i r) := ⟨Expr.inv⟩
instance : AndOp (Expr d i r) := ⟨Expr.and⟩
instance : OrOp (Expr d i r) := ⟨Expr.or⟩
instance : XorOp (Expr d i r) := ⟨Expr.xor⟩

@[simp] theorem eval_or (a b : Expr d i r) (xs s) :
    (a.or b).eval xs s = (a.eval xs s || b.eval xs s) := by
  simp [or, eval, Bool.not_and]

end Expr

/-- Little-endian word expressions: no implicit extension or truncation. -/
abbrev WordExpr (d i r w : Nat) := Vector (Expr d i r) w
namespace WordExpr

def literal (v : BitVec w) : WordExpr d i r w := Vector.ofFn fun k => .lit (v.getLsbD k.val)
def inputs (offset : Nat) (h : offset + w ≤ i) : WordExpr d i r w :=
  Vector.ofFn fun k => .input ⟨offset + k.val, by omega⟩
def registers (offset : Nat) (h : offset + w ≤ r) : WordExpr d i r w :=
  Vector.ofFn fun k => .reg ⟨offset + k.val, by omega⟩
def mux (c : Expr d i r) (a b : WordExpr d i r w) : WordExpr d i r w :=
  Vector.ofFn fun k => .mux c a[k] b[k]
def bitAnd (a b : WordExpr d i r w) : WordExpr d i r w := a.zipWith Expr.and b
def bitXor (a b : WordExpr d i r w) : WordExpr d i r w := a.zipWith Expr.xor b

def eq (a b : WordExpr d i r w) : Expr d i r :=
  (a.zipWith (fun x y => .inv (.xor x y)) b).foldl Expr.and (.lit true)

/-- Structural carry recurrence exposes a local proof obligation for each bit. -/
def carryAt (a b : WordExpr d i r w) (initial : Expr d i r) : Nat → Expr d i r
  | 0 => initial
  | n + 1 => if h : n < w then
      (Expr.and a[n] b[n]).or (.and (.xor a[n] b[n]) (carryAt a b initial n))
    else carryAt a b initial n

/-- Ripple-carry addition. Carry out is explicit, so overflow can be specified. -/
def addWithCarry (a b : WordExpr d i r w) (carry : Expr d i r := .lit false) :
    WordExpr d i r w × Expr d i r :=
  (Vector.ofFn (fun k => .xor (.xor a[k] b[k]) (carryAt a b carry k.val)), carryAt a b carry w)
def add (a b : WordExpr d i r w) : WordExpr d i r w := (addWithCarry a b).1

def eval (a : WordExpr d i r w) (xs : Fin i → Bool) (s : Fin r → Bool) : BitVec w :=
  BitVec.cast (by simp) (BitVec.ofBoolListLE ((a.map fun e => e.eval xs s).toList))
end WordExpr
end HDLean
