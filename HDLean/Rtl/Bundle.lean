import HDLean.Rtl.Tactic

/-!
# Typed records of words

A record of words is declared once, parameterized by what each field holds:

```
structure Regs (F : Nat → Type) where
  pc : F 8
  acc : F 16
```

`Regs BitVec` is the semantic state, `Regs Sig` the hardware handles inside a
builder program, and `Regs (fun _ => Reset)` the reset values. A `Bundle`
instance lists the fields; everything else (port declarations, reading the
store, decoding outputs) is generic.
-/
namespace HDLean.Rtl

/-- A heterogeneous vector indexed by widths. -/
inductive HVec (F : Nat → Type) : List Nat → Type where
  | nil : HVec F []
  | cons {w : Nat} {ws : List Nat} : F w → HVec F ws → HVec F (w :: ws)

namespace HVec

def head : HVec F (w :: ws) → F w
  | cons x _ => x

def tail : HVec F (w :: ws) → HVec F ws
  | cons _ xs => xs

@[simp] theorem head_cons (x : F w) (xs : HVec F ws) : (cons x xs).head = x := rfl
@[simp] theorem tail_cons (x : F w) (xs : HVec F ws) : (cons x xs).tail = xs := rfl

theorem eta : ∀ (v : HVec F (w :: ws)), v = cons v.head v.tail
  | cons _ _ => rfl

/-- A vector rebuilt from its heads and tails; equal to itself (`rebuild_eq`). -/
def rebuild : (ws : List Nat) → HVec F ws → HVec F ws
  | [], _ => nil
  | _ :: ws, v => cons v.head (rebuild ws v.tail)

theorem rebuild_eq : ∀ (ws : List Nat) (v : HVec F ws), rebuild ws v = v
  | [], nil => rfl
  | _ :: ws, cons x xs => by simp [rebuild, rebuild_eq ws xs]

def map (f : ∀ {w}, F w → G w) : HVec F ws → HVec G ws
  | nil => nil
  | cons x xs => cons (f x) (map f xs)

def zipWith (f : ∀ {w}, F w → G w → H w) : HVec F ws → HVec G ws → HVec H ws
  | nil, nil => nil
  | cons x xs, cons y ys => cons (f x y) (zipWith f xs ys)

def toList (f : ∀ {w}, F w → α) : HVec F ws → List α
  | nil => []
  | cons x xs => f x :: toList f xs

/-- Read consecutive raw values, starting at `base`, at the given widths. -/
def decode : (ws : List Nat) → (base : Nat) → (Nat → Nat) → HVec BitVec ws
  | [], _, _ => nil
  | w :: ws, base, f => cons (bv w (f base)) (decode ws (base + 1) f)

end HVec

/-- A record of words: its fields, in order, with names and widths. -/
class Bundle (R : (Nat → Type) → Type) where
  fields : List (String × Nat)
  toVec : {F : Nat → Type} → R F → HVec F (fields.map Prod.snd)
  ofVec : {F : Nat → Type} → HVec F (fields.map Prod.snd) → R F
  ofVec_toVec : ∀ {F : Nat → Type} (r : R F), ofVec (toVec r) = r
  toVec_ofVec : ∀ {F : Nat → Type} (v : HVec F (fields.map Prod.snd)), toVec (ofVec v) = v

namespace Bundle

abbrev widths (R : (Nat → Type) → Type) [Bundle R] : List Nat := (fields R).map Prod.snd

def ports (R : (Nat → Type) → Type) [Bundle R] : Array Port :=
  ((fields R).map fun p => (⟨Ident.ofString p.1, p.2⟩ : Port)).toArray

/-- Decode raw port or register values into a semantic record. -/
def decode (R : (Nat → Type) → Type) [Bundle R] (f : Nat → Nat) : R BitVec :=
  ofVec (HVec.decode (widths R) 0 f)

end Bundle

/-- Raw values of a semantic record, in field order. -/
def Bundle.encode {R : (Nat → Type) → Type} [Bundle R] (r : R BitVec) : Array Nat :=
  ((Bundle.toVec r).toList (fun x => x.toNat)).toArray

end HDLean.Rtl
