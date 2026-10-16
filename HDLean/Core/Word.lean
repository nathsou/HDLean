import HDLean.Core.Expr
import Init.Data.BitVec.Bitblast

namespace HDLean.WordExpr

@[simp] theorem eval_bit (a : WordExpr d i r w) (xs state) (k : Nat) (hk : k < w) :
    (a.eval xs state).getLsbD k = a[k].eval xs state := by
  simp only [eval, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD]
  rw [List.getElem?_eq_getElem (by simpa using hk)]
  simp

@[simp] theorem eval_literal (a : BitVec w) (xs : Fin i → Bool) (state : Fin r → Bool) :
    (literal a : WordExpr d i r w).eval xs state = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h := eval_bit (literal a : WordExpr d i r w) xs state k hk
  simpa only [literal, Vector.getElem_ofFn, Expr.eval] using h

@[simp] theorem eval_mux (c : Expr d i r) (a b : WordExpr d i r w) (xs state) :
    (mux c a b).eval xs state = if c.eval xs state then a.eval xs state else b.eval xs state := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h := eval_bit (mux c a b) xs state k hk
  rw [h]
  cases hc : c.eval xs state <;> simp [mux, Expr.eval, hc, eval_bit a xs state k hk, eval_bit b xs state k hk]

@[simp] theorem carryAt_correct (a b : WordExpr d i r w) (initial : Expr d i r)
    (n : Nat) (hn : n ≤ w) (xs state) :
    (carryAt a b initial n).eval xs state =
      BitVec.carry n (a.eval xs state) (b.eval xs state) (initial.eval xs state) := by
  induction n with
  | zero => simp [carryAt]
  | succ n ih =>
    have hl : n < w := by omega
    rw [carryAt]
    simp only [hl, ↓reduceDIte, Expr.eval_or, Expr.eval, ih (by omega), BitVec.carry_succ]
    rw [show (a.eval xs state).getLsbD n = (a[n]'hl).eval xs state from eval_bit a xs state n hl,
      show (b.eval xs state).getLsbD n = (b[n]'hl).eval xs state from eval_bit b xs state n hl]
    cases (a[n]'hl).eval xs state <;> cases (b[n]'hl).eval xs state <;>
      cases BitVec.carry n (a.eval xs state) (b.eval xs state) (initial.eval xs state) <;> rfl

/-- The structural adder implements modular addition, including an explicit carry-in. -/
theorem addWithCarry_correct (a b : WordExpr d i r w) (initial : Expr d i r) (xs state) :
    (addWithCarry a b initial).1.eval xs state =
      a.eval xs state + b.eval xs state + (BitVec.ofBool (initial.eval xs state)).setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h := eval_bit (addWithCarry a b initial).1 xs state k hk
  rw [h, BitVec.getLsbD_add_add_bool hk, eval_bit a xs state k hk, eval_bit b xs state k hk]
  simp [addWithCarry, Expr.eval]
  exact carryAt_correct a b initial k (by omega) xs state

@[simp] theorem add_correct (a b : WordExpr d i r w) (xs state) :
    (add a b).eval xs state = a.eval xs state + b.eval xs state := by
  simpa [add, Expr.eval] using addWithCarry_correct a b (.lit false) xs state

/-- Carry-out has the standard mathematical overflow semantics. -/
theorem addWithCarry_overflow (a b : WordExpr d i r w) (initial : Expr d i r) (xs state) :
    (addWithCarry a b initial).2.eval xs state =
      BitVec.carry w (a.eval xs state) (b.eval xs state) (initial.eval xs state) := by
  exact carryAt_correct a b initial w (by omega) xs state

instance : HAdd (WordExpr d i r w) (WordExpr d i r w) (WordExpr d i r w) := ⟨add⟩
instance (n : Nat) : OfNat (WordExpr d i r w) n := ⟨literal (BitVec.ofNat w n)⟩

@[simp] theorem eval_hAdd (a b : WordExpr d i r w) (xs state) :
    (a + b).eval xs state = a.eval xs state + b.eval xs state := add_correct a b xs state

@[simp] theorem eval_ofNat (n : Nat) (xs : Fin i → Bool) (state : Fin r → Bool) :
    (OfNat.ofNat n : WordExpr d i r w).eval xs state = BitVec.ofNat w n :=
  eval_literal _ xs state

def bitNot (a : WordExpr d i r w) : WordExpr d i r w := a.map Expr.inv
def bitOr (a b : WordExpr d i r w) : WordExpr d i r w := a.zipWith Expr.or b

@[simp] theorem bitNot_correct (a : WordExpr d i r w) (xs state) :
    (bitNot a).eval xs state = ~~~a.eval xs state := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [eval_bit _ _ _ k hk, BitVec.getLsbD_not, eval_bit a xs state k hk]
  simp [bitNot, Expr.eval, hk]

@[simp] theorem bitAnd_correct (a b : WordExpr d i r w) (xs state) :
    (bitAnd a b).eval xs state = a.eval xs state &&& b.eval xs state := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [eval_bit _ _ _ k hk, BitVec.getLsbD_and, eval_bit a xs state k hk, eval_bit b xs state k hk]
  simp [bitAnd, Expr.eval]

@[simp] theorem bitOr_correct (a b : WordExpr d i r w) (xs state) :
    (bitOr a b).eval xs state = a.eval xs state ||| b.eval xs state := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [eval_bit _ _ _ k hk, BitVec.getLsbD_or, eval_bit a xs state k hk, eval_bit b xs state k hk]
  simp [bitOr]

@[simp] theorem bitXor_correct (a b : WordExpr d i r w) (xs state) :
    (bitXor a b).eval xs state = a.eval xs state ^^^ b.eval xs state := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [eval_bit _ _ _ k hk, BitVec.getLsbD_xor, eval_bit a xs state k hk, eval_bit b xs state k hk]
  simp [bitXor, Expr.eval]

def sub (a b : WordExpr d i r w) : WordExpr d i r w :=
  (addWithCarry a (bitNot b) (.lit true)).1

@[simp] theorem sub_correct (a b : WordExpr d i r w) (xs state) :
    (sub a b).eval xs state = a.eval xs state - b.eval xs state := by
  rw [sub, addWithCarry_correct, bitNot_correct, BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add]
  simp [Expr.eval, BitVec.add_assoc, BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (v := 1) (by decide)]

def ult (a b : WordExpr d i r w) : Expr d i r :=
  .inv (carryAt a (bitNot b) (.lit true) w)

@[simp] theorem ult_correct (a b : WordExpr d i r w) (xs state) :
    (ult a b).eval xs state = (a.eval xs state).ult (b.eval xs state) := by
  simp [ult, Expr.eval, carryAt_correct, BitVec.ult_eq_not_carry]

def extract (a : WordExpr d i r w) (offset len : Nat) (h : offset + len ≤ w) : WordExpr d i r len :=
  Vector.ofFn fun k => a[offset + k.val]'(by omega)

@[simp] theorem extract_correct (a : WordExpr d i r w) (offset len : Nat) (h : offset + len ≤ w)
    (xs state) : (extract a offset len h).eval xs state = (a.eval xs state).extractLsb' offset len := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [eval_bit _ _ _ k hk, BitVec.getLsbD_extractLsb', eval_bit a xs state (offset+k) (by omega)]
  simp [extract, hk]

def setWidth (a : WordExpr d i r w) (size : Nat) : WordExpr d i r size :=
  Vector.ofFn fun k => if h : k.val < w then a[k.val] else .lit false

@[simp] theorem setWidth_correct (a : WordExpr d i r w) (size : Nat) (xs state) :
    (setWidth a size).eval xs state = (a.eval xs state).setWidth size := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [eval_bit _ _ _ k hk, BitVec.getLsbD_setWidth]
  by_cases hw : k < w
  · simp only [setWidth, Vector.getElem_ofFn, hw, ↓reduceDIte, hk, decide_true, Bool.true_and]
    exact (eval_bit a xs state k hw).symm
  · simp only [setWidth, Vector.getElem_ofFn, hw, ↓reduceDIte, hk, decide_true, Bool.true_and, Expr.eval]
    exact (BitVec.getLsbD_of_ge (a.eval xs state) k (by omega)).symm

def signExtend (a : WordExpr d i r w) (size : Nat) : WordExpr d i r size :=
  Vector.ofFn fun k => if h : k.val < w then a[k.val]
    else if h : 0 < w then a[w - 1]'(by omega) else .lit false

@[simp] theorem signExtend_correct (a : WordExpr d i r w) (size : Nat) (xs state) :
    (signExtend a size).eval xs state = (a.eval xs state).signExtend size := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [eval_bit _ _ _ k hk, BitVec.getLsbD_signExtend]
  by_cases hw : k < w
  · simp only [signExtend, Vector.getElem_ofFn, hw, ↓reduceDIte, hk, decide_true, Bool.true_and]
    exact (eval_bit a xs state k hw).symm
  · by_cases hp : 0 < w
    · simp [signExtend, hk, hw, hp, BitVec.msb, BitVec.getMsbD,
        eval_bit a xs state (w-1) (by omega)]
    · have hz : w = 0 := by omega
      subst w
      simp [signExtend, hk, Expr.eval, BitVec.msb, BitVec.getMsbD]

private theorem not_xor_true (a b : Bool) : (!(a ^^ b)) = true ↔ a = b := by
  cases a <;> cases b <;> decide

def equalPrefix (a b : WordExpr d i r w) : Nat → Expr d i r
  | 0 => .lit true
  | n + 1 => if h : n < w then
      .and (equalPrefix a b n) (.inv (.xor a[n] b[n])) else equalPrefix a b n

theorem equalPrefix_correct (a b : WordExpr d i r w) (n : Nat) (hn : n ≤ w) (xs state) :
    (equalPrefix a b n).eval xs state = true ↔ ∀ k, k < n →
      (a.eval xs state).getLsbD k = (b.eval xs state).getLsbD k := by
  induction n with
  | zero => simp [equalPrefix, Expr.eval]
  | succ n ih =>
    have hl : n < w := by omega
    simp only [equalPrefix, hl, ↓reduceDIte, Expr.eval, Bool.and_eq_true, not_xor_true, ih (by omega)]
    rw [← eval_bit a xs state n hl, ← eval_bit b xs state n hl]
    constructor
    · rintro ⟨h, he⟩ k hk
      by_cases hn : k = n
      · simpa [hn] using he
      · exact h k (by omega)
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

def equal (a b : WordExpr d i r w) : Expr d i r := equalPrefix a b w

@[simp] theorem equal_correct (a b : WordExpr d i r w) (xs state) :
    (equal a b).eval xs state = decide (a.eval xs state = b.eval xs state) := by
  apply Bool.eq_iff_iff.mpr
  rw [equal, equalPrefix_correct a b w (by omega)]
  simp only [decide_eq_true_eq]
  constructor
  · exact BitVec.eq_of_getLsbD_eq
  · intro h k hk
    rw [h]

instance : HSub (WordExpr d i r w) (WordExpr d i r w) (WordExpr d i r w) := ⟨sub⟩
instance : Complement (WordExpr d i r w) := ⟨bitNot⟩
instance : AndOp (WordExpr d i r w) := ⟨bitAnd⟩
instance : OrOp (WordExpr d i r w) := ⟨bitOr⟩
instance : XorOp (WordExpr d i r w) := ⟨bitXor⟩

end HDLean.WordExpr
