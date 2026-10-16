import HDLean.Rtl.Blast.ToDag
import HDLean.Rtl.Semantics

/-!
# Bit-vectors in an AIG

`Denotes aig assign bits x`: the raw fanins `bits` are in range and denote the
bits of `x`. Operators from Lean's verified bit-blaster (`Std.Tactic.BVDecide`)
are wrapped once (`vop1`, `vop2`, `vshift`) with a generic correctness lemma;
rewiring operators (slices, concatenation, extensions) add no gates.
-/
namespace HDLean.Rtl.Blast
open Std.Sat Std.Sat.AIG Std.Tactic.BVDecide

abbrev Bits := Array Fanin

@[simp] theorem bv_ofNat_toNat (x : BitVec w) : bv w x.toNat = x := by simp [bv]

/-- `bits` denote `x`. -/
def Denotes (aig : AIG Nat) (assign : Nat → Bool) (bits : Bits) (x : BitVec w) : Prop :=
  ∃ rv : RefVec aig w, rv.refs.toArray = bits ∧ ∀ idx (hidx : idx < w), ⟦aig, rv.get idx hidx, assign⟧ = x.getLsbD idx

/-- A checked view of raw fanins as a `RefVec`. -/
def toVec (aig : AIG Nat) (bits : Bits) (w : Nat) : Option (RefVec aig w) :=
  if h : bits.size = w ∧ ∀ i (hi : i < bits.size), bits[i].gate < aig.decls.size then
    some ⟨⟨bits, h.1⟩, fun {i} hi => h.2 i (h.1 ▸ hi)⟩
  else none

theorem toVec_of_denotes {aig : AIG Nat} {assign : Nat → Bool} {bits : Bits} {x : BitVec w}
    (h : Denotes aig assign bits x) :
    ∃ rv : RefVec aig w, toVec aig bits w = some rv ∧ ∀ idx (hidx : idx < w), ⟦aig, rv.get idx hidx, assign⟧ = x.getLsbD idx := by
  obtain ⟨rv, hr, hd⟩ := h
  have hs : bits.size = w := by rw [← hr]; simp
  have hb : ∀ i (hi : i < bits.size), bits[i].gate < aig.decls.size := by
    intro i hi
    have := rv.hrefs (i := i) (by omega)
    subst hr
    simpa using this
  refine ⟨rv, ?_, hd⟩
  simp only [toVec, hs, hb, implies_true, and_self, dite_true, Option.some.injEq]
  cases rv
  subst hr
  rfl

theorem Denotes.mono {aig aig' : AIG Nat} {assign : Nat → Bool} {bits : Bits} {x : BitVec w}
    (h : Denotes aig assign bits x) (hp : IsPrefix aig.decls aig'.decls) : Denotes aig' assign bits x := by
  obtain ⟨rv, hr, hd⟩ := h
  refine ⟨rv.cast hp.size_le, by simpa [RefVec.cast, RefVec.cast'] using hr, fun idx hidx => ?_⟩
  rw [← hd idx hidx]
  exact denote.eq_of_isPrefix ⟨aig, rv.get idx hidx⟩ aig' hp

theorem IsPrefix.refl' (aig : AIG Nat) : IsPrefix aig.decls aig.decls := IsPrefix.rfl

theorem IsPrefix.trans' {a b c : AIG Nat} (h1 : IsPrefix a.decls b.decls) (h2 : IsPrefix b.decls c.decls) :
    IsPrefix a.decls c.decls :=
  ⟨Nat.le_trans h1.size_le h2.size_le, fun idx h => by
    rw [h2.idx_eq idx (by have := h1.size_le; omega), h1.idx_eq idx h]⟩

/-! ## Gate-producing operators -/

/-- A vector operator from the verified bit-blaster, applied to checked inputs. -/
def vop1 (f : {len : Nat} → (aig : AIG Nat) → RefVec aig len → RefVecEntry Nat len) (a : Bits) (w : Nat)
    (aig : AIG Nat) : Option (Bits × AIG Nat) := do
  let va ← toVec aig a w
  let r := f aig va
  pure (r.vec.refs.toArray, r.aig)

def vop2 (f : {len : Nat} → (aig : AIG Nat) → BinaryRefVec aig len → RefVecEntry Nat len) (a b : Bits) (w : Nat)
    (aig : AIG Nat) : Option (Bits × AIG Nat) := do
  let va ← toVec aig a w
  let vb ← toVec aig b w
  let r := f aig ⟨va, vb⟩
  pure (r.vec.refs.toArray, r.aig)

def vshift (f : {len : Nat} → (aig : AIG Nat) → ArbitraryShiftTarget aig len → RefVecEntry Nat len)
    (a b : Bits) (w v : Nat) (aig : AIG Nat) : Option (Bits × AIG Nat) := do
  let va ← toVec aig a w
  let vb ← toVec aig b v
  let r := f aig ⟨v, va, vb⟩
  pure (r.vec.refs.toArray, r.aig)

/-- The result of a step: new bits denoting `x` in an extension of the AIG. -/
def Yields (aig : AIG Nat) (assign : Nat → Bool) (r : Option (Bits × AIG Nat)) (x : BitVec w) : Prop :=
  ∃ bits aig', r = some (bits, aig') ∧ IsPrefix aig.decls aig'.decls ∧ Denotes aig' assign bits x

private theorem entry_denotes {assign : Nat → Bool} (r : RefVecEntry Nat w) (x : BitVec w)
    (h : ∀ idx (hidx : idx < w), ⟦r.aig, r.vec.get idx hidx, assign⟧ = x.getLsbD idx) :
    Denotes r.aig assign r.vec.refs.toArray x :=
  ⟨r.vec, rfl, h⟩

theorem vop1_ok (f : {len : Nat} → (aig : AIG Nat) → RefVec aig len → RefVecEntry Nat len)
    [LawfulVecOperator Nat RefVec f] (op : BitVec w → BitVec w)
    (hf : ∀ (aig : AIG Nat) (input : RefVec aig w) (x : BitVec w) (assign : Nat → Bool),
      (∀ idx (hidx : idx < w), ⟦aig, input.get idx hidx, assign⟧ = x.getLsbD idx) →
      ∀ idx (hidx : idx < w), ⟦(f aig input).aig, (f aig input).vec.get idx hidx, assign⟧ = (op x).getLsbD idx)
    {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {x : BitVec w} (ha : Denotes aig assign a x) :
    Yields aig assign (vop1 f a w aig) (op x) := by
  obtain ⟨va, hva, hda⟩ := toVec_of_denotes ha
  refine ⟨_, _, by simp [vop1, hva], LawfulVecOperator.isPrefix_aig aig va,
    entry_denotes (f aig va) _ (hf aig va x assign hda)⟩

theorem vop2_ok (f : {len : Nat} → (aig : AIG Nat) → BinaryRefVec aig len → RefVecEntry Nat len)
    [LawfulVecOperator Nat BinaryRefVec f] (op : BitVec w → BitVec w → BitVec w)
    (hf : ∀ (aig : AIG Nat) (input : BinaryRefVec aig w) (x y : BitVec w) (assign : Nat → Bool),
      (∀ idx (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign⟧ = x.getLsbD idx) →
      (∀ idx (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign⟧ = y.getLsbD idx) →
      ∀ idx (hidx : idx < w), ⟦(f aig input).aig, (f aig input).vec.get idx hidx, assign⟧ = (op x y).getLsbD idx)
    {aig : AIG Nat} {assign : Nat → Bool} {a b : Bits} {x y : BitVec w}
    (ha : Denotes aig assign a x) (hb : Denotes aig assign b y) :
    Yields aig assign (vop2 f a b w aig) (op x y) := by
  obtain ⟨va, hva, hda⟩ := toVec_of_denotes ha
  obtain ⟨vb, hvb, hdb⟩ := toVec_of_denotes hb
  let input : BinaryRefVec aig w := ⟨va, vb⟩
  refine ⟨_, _, by simp [vop2, hva, hvb]; exact ⟨rfl, rfl⟩, LawfulVecOperator.isPrefix_aig aig input,
    entry_denotes (f aig input) _ (hf aig input x y assign hda hdb)⟩

theorem vshift_ok (f : {len : Nat} → (aig : AIG Nat) → ArbitraryShiftTarget aig len → RefVecEntry Nat len)
    [LawfulVecOperator Nat ArbitraryShiftTarget f] (op : BitVec w → BitVec v → BitVec w)
    (hf : ∀ (aig : AIG Nat) (target : ArbitraryShiftTarget aig w) (x : BitVec w) (y : BitVec target.n)
      (assign : Nat → Bool) (hn : target.n = v),
      (∀ idx (hidx : idx < w), ⟦aig, target.target.get idx hidx, assign⟧ = x.getLsbD idx) →
      (∀ idx (hidx : idx < target.n), ⟦aig, target.distance.get idx hidx, assign⟧ = y.getLsbD idx) →
      ∀ idx (hidx : idx < w), ⟦(f aig target).aig, (f aig target).vec.get idx hidx, assign⟧ =
        (op x (hn ▸ y)).getLsbD idx)
    {aig : AIG Nat} {assign : Nat → Bool} {a b : Bits} {x : BitVec w} {y : BitVec v}
    (ha : Denotes aig assign a x) (hb : Denotes aig assign b y) :
    Yields aig assign (vshift f a b w v aig) (op x y) := by
  obtain ⟨va, hva, hda⟩ := toVec_of_denotes ha
  obtain ⟨vb, hvb, hdb⟩ := toVec_of_denotes hb
  let target : ArbitraryShiftTarget aig w := ⟨v, va, vb⟩
  refine ⟨_, _, by simp [vshift, hva, hvb]; exact ⟨rfl, rfl⟩, LawfulVecOperator.isPrefix_aig aig target,
    entry_denotes (f aig target) _ (hf aig target x y assign rfl hda hdb)⟩


/-! ## Bits from existing fanins -/

def fconst (b : Bool) : Fanin := Fanin.mk 0 b

theorem Denotes.size {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {x : BitVec w}
    (h : Denotes aig assign a x) : a.size = w := by
  obtain ⟨rv, hr, _⟩ := h; rw [← hr]; simp

theorem Denotes.bit {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {x : BitVec w}
    (h : Denotes aig assign a x) (i : Nat) (hi : i < a.size) :
    ∃ hb : a[i].gate < aig.decls.size, ⟦aig, ⟨a[i].gate, a[i].invert, hb⟩, assign⟧ = x.getLsbD i := by
  obtain ⟨rv, hr, hd⟩ := h
  have hs : a.size = w := by rw [← hr]; simp
  subst hr
  exact ⟨rv.hrefs (by omega), by simpa [RefVec.get] using hd i (by omega)⟩

theorem const_bit (aig : AIG Nat) (assign : Nat → Bool) (b : Bool) :
    ∃ hb : (fconst b).gate < aig.decls.size, ⟦aig, ⟨(fconst b).gate, (fconst b).invert, hb⟩, assign⟧ = b := by
  have hg : (fconst b).gate = 0 := Fanin.gate_mk
  have hi : (fconst b).invert = b := Fanin.invert_mk
  refine ⟨by rw [hg]; exact aig.hzero, ?_⟩
  simp only [hi]
  have := denote_idx_false (aig := aig) (start := 0) (invert := b) (assign := assign) (hstart := aig.hzero) aig.hconst
  simpa [hg] using this

/-- Bits chosen one by one, each denoting the matching bit of `x`. -/
theorem denotes_ofFn (aig : AIG Nat) (assign : Nat → Bool) (f : Fin w → Fanin) (x : BitVec w)
    (h : ∀ i : Fin w, ∃ hb : (f i).gate < aig.decls.size, ⟦aig, ⟨(f i).gate, (f i).invert, hb⟩, assign⟧ = x.getLsbD i) :
    Denotes aig assign (Array.ofFn f) x := by
  refine ⟨⟨⟨Array.ofFn f, by simp⟩, fun {i} hi => by simpa using (h ⟨i, hi⟩).1⟩, rfl, fun idx hidx => ?_⟩
  obtain ⟨_, hd⟩ := h ⟨idx, hidx⟩
  simpa [RefVec.get] using hd

def constBits (w v : Nat) : Bits := Array.ofFn (n := w) fun i => fconst (v.testBit i)

theorem constBits_ok (aig : AIG Nat) (assign : Nat → Bool) (w v : Nat) :
    Denotes aig assign (constBits w v) (bv w v) := by
  apply denotes_ofFn
  intro i
  obtain ⟨hb, hd⟩ := const_bit aig assign (v.testBit i)
  exact ⟨hb, by rw [hd, bv, BitVec.getLsbD_ofNat]; simp [i.isLt]⟩

/-- Bit `i` of `a`, or a constant beyond its width. -/
def bitOr (a : Bits) (i : Nat) (b : Bool) : Fanin := if h : i < a.size then a[i] else fconst b

theorem bitOr_ok {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {x : BitVec w} (h : Denotes aig assign a x)
    (i : Nat) (b : Bool) :
    ∃ hb : (bitOr a i b).gate < aig.decls.size, ⟦aig, ⟨(bitOr a i b).gate, (bitOr a i b).invert, hb⟩, assign⟧ =
      if i < w then x.getLsbD i else b := by
  unfold bitOr
  have hs := h.size
  split
  · rename_i hi
    obtain ⟨hb, hd⟩ := h.bit i hi
    exact ⟨hb, by rw [hd, if_pos (by omega)]⟩
  · rename_i hi
    obtain ⟨hb, hd⟩ := const_bit aig assign b
    exact ⟨hb, by rw [hd, if_neg (by omega)]⟩

def sliceBits (a : Bits) (lo w : Nat) : Bits := Array.ofFn (n := w) fun i => bitOr a (lo + i) false

theorem sliceBits_ok {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {wa : Nat} (n lo w : Nat)
    (h : Denotes aig assign a (bv wa n)) (hn : n < 2 ^ wa) :
    Denotes aig assign (sliceBits a lo w) (bv w (n >>> lo)) := by
  apply denotes_ofFn
  intro i
  obtain ⟨hb, hd⟩ := bitOr_ok h (lo + i) false
  refine ⟨hb, ?_⟩
  rw [hd]
  simp only [bv, BitVec.getLsbD_ofNat, i.isLt, decide_true, Bool.true_and, Nat.testBit_shiftRight]
  split
  · rename_i hlt; simp [hlt]
  · rename_i hge
    symm
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega))

def zextBits (a : Bits) (w : Nat) : Bits := Array.ofFn (n := w) fun i => bitOr a i false

theorem zextBits_ok {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {wa : Nat} (n w : Nat)
    (h : Denotes aig assign a (bv wa n)) (hn : n < 2 ^ wa) :
    Denotes aig assign (zextBits a w) (bv w n) := by
  have := sliceBits_ok n 0 w h hn
  simpa [sliceBits, zextBits] using this

def sextBits (a : Bits) (w : Nat) : Bits :=
  Array.ofFn (n := w) fun (i : Fin w) => if h : i.val < a.size then a[i.val] else
    if h' : 0 < a.size then a[a.size - 1] else fconst false

theorem sextBits_ok {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {x : BitVec fw} (w : Nat)
    (h : Denotes aig assign a x) :
    Denotes aig assign (sextBits a w) (x.signExtend w) := by
  have hs := h.size
  apply denotes_ofFn
  intro i
  show ∃ hb, _ = _
  rw [BitVec.getLsbD_signExtend]
  simp only [i.isLt, decide_true, Bool.true_and]
  split
  · rename_i hi
    obtain ⟨hb, hd⟩ := h.bit i hi
    exact ⟨hb, by rw [hd, if_pos (by omega)]⟩
  · rename_i hi
    rw [if_neg (by omega)]
    split
    · rename_i hpos
      obtain ⟨hb, hd⟩ := h.bit (a.size - 1) (by omega)
      refine ⟨hb, ?_⟩
      rw [hd, BitVec.msb_eq_getLsbD_last]
      congr 1
      omega
    · rename_i hz
      have hfw : fw = 0 := by omega
      subst hfw
      obtain ⟨hb, hd⟩ := const_bit aig assign false
      exact ⟨hb, by rw [hd]; simp [BitVec.msb]⟩

/-- `hi ++ lo`, low bits first. -/
def concatBits (h l : Bits) : Bits := l ++ h

theorem concatBits_ok {aig : AIG Nat} {assign : Nat → Bool} {h l : Bits} {x : BitVec wh} {y : BitVec wl}
    (hh : Denotes aig assign h x) (hl : Denotes aig assign l y) :
    Denotes aig assign (concatBits h l) (x ++ y) := by
  have hsh := hh.size
  have hsl := hl.size
  have heq : concatBits h l = Array.ofFn (n := wh + wl) fun i => if i.val < wl then bitOr l i false else bitOr h (i - wl) false := by
    apply Array.ext
    · simp [concatBits]; omega
    · intro i h1 h2
      have h1' : i < wh + wl := by simp [concatBits] at h1; omega
      simp only [concatBits, Array.getElem_ofFn]
      split
      · rename_i hi
        rw [Array.getElem_append_left (by omega)]
        simp only [bitOr, dif_pos (show i < l.size by omega)]
      · rename_i hi
        rw [Array.getElem_append_right (by omega)]
        simp only [bitOr, dif_pos (show i - wl < h.size by omega), hsl]
  rw [heq]
  apply denotes_ofFn
  intro i
  rw [BitVec.getLsbD_append]
  split
  · rename_i hi
    obtain ⟨hb, hd⟩ := bitOr_ok hl i false
    exact ⟨hb, by rw [hd, if_pos hi]⟩
  · rename_i hi
    obtain ⟨hb, hd⟩ := bitOr_ok hh (i - wl) false
    exact ⟨hb, by rw [hd, if_pos (by omega)]⟩


/-! ## Single bits, multiplexers, bitwise operators -/

def bitOf (f : Fanin) : Bits := #[f]

theorem bitOf_ok {aig : AIG Nat} {assign : Nat → Bool} (f : Fanin) (c : Bool)
    (h : ∃ hb : f.gate < aig.decls.size, ⟦aig, ⟨f.gate, f.invert, hb⟩, assign⟧ = c) :
    Denotes aig assign (bitOf f) (BitVec.ofBool c) := by
  have : bitOf f = Array.ofFn (n := 1) fun _ => f := by
    apply Array.ext
    · simp [bitOf]
    · intro i h1 h2; simp only [bitOf, List.size_toArray, List.length_cons, List.length_nil] at h1
      have : i = 0 := by omega
      subst this; rfl
  rw [this]
  apply denotes_ofFn
  intro i
  obtain ⟨hb, hd⟩ := h
  have hi : i.val = 0 := by omega
  exact ⟨hb, by rw [hd, hi]; simp⟩

theorem entry_bit (e : Entrypoint Nat) (assign : Nat → Bool) :
    ∃ hb : (Fanin.mk e.ref.gate e.ref.invert).gate < e.aig.decls.size,
      ⟦e.aig, ⟨(Fanin.mk e.ref.gate e.ref.invert).gate, (Fanin.mk e.ref.gate e.ref.invert).invert, hb⟩, assign⟧ =
        ⟦e, assign⟧ := by
  refine ⟨by rw [Fanin.gate_mk]; exact e.ref.hgate, ?_⟩
  simp only [Fanin.gate_mk, Fanin.invert_mk]

/-- A comparison producing one bit. -/
def bit2 (f : (aig : AIG Nat) → BinaryRefVec aig w → Entrypoint Nat) (a b : Bits) (aig : AIG Nat) :
    Option (Bits × AIG Nat) := do
  let va ← toVec aig a w
  let vb ← toVec aig b w
  let e := f aig ⟨va, vb⟩
  pure (bitOf (Fanin.mk e.ref.gate e.ref.invert), e.aig)

theorem bit2_ok (f : (aig : AIG Nat) → BinaryRefVec aig w → Entrypoint Nat)
    [LawfulOperator Nat (BinaryRefVec · w) f] (P : BitVec w → BitVec w → Bool)
    (hf : ∀ (aig : AIG Nat) (input : BinaryRefVec aig w) (x y : BitVec w) (assign : Nat → Bool),
      (∀ idx (hidx : idx < w), ⟦aig, input.lhs.get idx hidx, assign⟧ = x.getLsbD idx) →
      (∀ idx (hidx : idx < w), ⟦aig, input.rhs.get idx hidx, assign⟧ = y.getLsbD idx) →
      ⟦f aig input, assign⟧ = P x y)
    {aig : AIG Nat} {assign : Nat → Bool} {a b : Bits} {x y : BitVec w}
    (ha : Denotes aig assign a x) (hb : Denotes aig assign b y) :
    Yields aig assign (bit2 f a b aig) (BitVec.ofBool (P x y)) := by
  obtain ⟨va, hva, hda⟩ := toVec_of_denotes ha
  obtain ⟨vb, hvb, hdb⟩ := toVec_of_denotes hb
  let input : BinaryRefVec aig w := ⟨va, vb⟩
  refine ⟨bitOf (Fanin.mk (f aig input).ref.gate (f aig input).ref.invert), (f aig input).aig,
    by simp [bit2, hva, hvb]; exact ⟨rfl, rfl⟩, LawfulOperator.isPrefix_aig (f := f) aig input, ?_⟩
  obtain ⟨hbd, hd⟩ := entry_bit (f aig input) assign
  exact bitOf_ok _ _ ⟨hbd, by rw [hd, hf aig input x y assign hda hdb]⟩

/-- Negate a single-bit result without a gate. -/
def bitNot (a : Bits) : Bits := a.map (·.flip true)

theorem bitNot_ok {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {c : Bool}
    (h : Denotes aig assign a (BitVec.ofBool c)) : Denotes aig assign (bitNot a) (BitVec.ofBool !c) := by
  have hs := h.size
  have heq : bitNot a = bitOf ((a[0]'(by omega)).flip true) := by
    apply Array.ext <;> simp [bitNot, bitOf, hs]
    intro i hi; have : i = 0 := by omega
    subst this; rfl
  rw [heq]
  obtain ⟨hb, hd⟩ := h.bit 0 (by omega)
  apply bitOf_ok
  refine ⟨by rw [Fanin.gate_flip]; exact hb, ?_⟩
  simp only [Fanin.gate_flip, Fanin.invert_flip]
  rw [denote_inv, Bool.xor_true]
  rw [denote_inv] at hd
  simp only [BitVec.getLsbD_ofBool, decide_true, Bool.true_and] at hd
  rw [← hd]
  cases a[0].invert <;> simp

/-- A two-input gate on single bits. -/
def gate2 (f : (aig : AIG Nat) → BinaryInput aig → Entrypoint Nat) (p q : Fanin) (aig : AIG Nat) :
    Option (Fanin × AIG Nat) :=
  if h : p.gate < aig.decls.size ∧ q.gate < aig.decls.size then
    let e := f aig ⟨⟨p.gate, p.invert, h.1⟩, ⟨q.gate, q.invert, h.2⟩⟩
    some (Fanin.mk e.ref.gate e.ref.invert, e.aig)
  else none

/-- The bit `f` denotes `c`. -/
def BitIs (aig : AIG Nat) (assign : Nat → Bool) (f : Fanin) (c : Bool) : Prop :=
  ∃ hb : f.gate < aig.decls.size, ⟦aig, ⟨f.gate, f.invert, hb⟩, assign⟧ = c

theorem BitIs.mono {aig aig' : AIG Nat} {assign : Nat → Bool} {f : Fanin} {c : Bool}
    (h : BitIs aig assign f c) (hp : IsPrefix aig.decls aig'.decls) : BitIs aig' assign f c := by
  obtain ⟨hb, hd⟩ := h
  exact ⟨by have := hp.size_le; omega, by rw [← hd]; exact denote.eq_of_isPrefix ⟨aig, ⟨f.gate, f.invert, hb⟩⟩ aig' hp⟩

theorem gate2_ok (f : (aig : AIG Nat) → BinaryInput aig → Entrypoint Nat) [LawfulOperator Nat BinaryInput f]
    (op : Bool → Bool → Bool)
    (hf : ∀ (aig : AIG Nat) (input : BinaryInput aig) (assign : Nat → Bool),
      ⟦f aig input, assign⟧ = op ⟦aig, input.lhs, assign⟧ ⟦aig, input.rhs, assign⟧)
    {aig : AIG Nat} {assign : Nat → Bool} {p q : Fanin} {c d : Bool}
    (hp : BitIs aig assign p c) (hq : BitIs aig assign q d) :
    ∃ r aig', gate2 f p q aig = some (r, aig') ∧ IsPrefix aig.decls aig'.decls ∧ BitIs aig' assign r (op c d) := by
  obtain ⟨hpb, hpd⟩ := hp
  obtain ⟨hqb, hqd⟩ := hq
  let input : BinaryInput aig := ⟨⟨p.gate, p.invert, hpb⟩, ⟨q.gate, q.invert, hqb⟩⟩
  refine ⟨Fanin.mk (f aig input).ref.gate (f aig input).ref.invert, (f aig input).aig,
    by simp [gate2, hpb, hqb]; exact ⟨rfl, rfl⟩, LawfulOperator.isPrefix_aig (f := f) aig input, ?_⟩
  obtain ⟨hb, hd⟩ := entry_bit (f aig input) assign
  exact ⟨hb, by rw [hd, hf]; simp only [input]; rw [hpd, hqd]⟩

/-- Vector multiplexer on a selector bit. -/
def vite (s : Fanin) (a b : Bits) (w : Nat) (aig : AIG Nat) : Option (Bits × AIG Nat) :=
  if hs : s.gate < aig.decls.size then do
    let va ← toVec aig a w
    let vb ← toVec aig b w
    let r := RefVec.ite aig ⟨⟨s.gate, s.invert, hs⟩, va, vb⟩
    pure (r.vec.refs.toArray, r.aig)
  else none

theorem vite_ok {aig : AIG Nat} {assign : Nat → Bool} {s : Fanin} {c : Bool} {a b : Bits} {x y : BitVec w}
    (hs : BitIs aig assign s c) (ha : Denotes aig assign a x) (hb : Denotes aig assign b y) :
    Yields aig assign (vite s a b w aig) (if c then x else y) := by
  obtain ⟨hsb, hsd⟩ := hs
  obtain ⟨va, hva, hda⟩ := toVec_of_denotes ha
  obtain ⟨vb, hvb, hdb⟩ := toVec_of_denotes hb
  let input : RefVec.IfInput aig w := ⟨⟨s.gate, s.invert, hsb⟩, va, vb⟩
  refine ⟨(RefVec.ite aig input).vec.refs.toArray, (RefVec.ite aig input).aig,
    by simp [vite, hsb, hva, hvb]; exact ⟨rfl, rfl⟩, LawfulVecOperator.isPrefix_aig (f := RefVec.ite) aig input, ?_⟩
  refine ⟨(RefVec.ite aig input).vec, rfl, fun idx hidx => ?_⟩
  rw [RefVec.denote_ite]
  simp only [input]
  rw [hsd]
  cases c <;> simp [hda, hdb]

/-- Bitwise operator from a two-input gate. -/
def vzip (func : (aig : AIG Nat) → BinaryInput aig → Entrypoint Nat) [LawfulOperator Nat BinaryInput func]
    [RefVec.LawfulZipOperator Nat func] (a b : Bits) (w : Nat) (aig : AIG Nat) : Option (Bits × AIG Nat) := do
  let va ← toVec aig a w
  let vb ← toVec aig b w
  let r := RefVec.zip aig ⟨va, vb⟩ func
  pure (r.vec.refs.toArray, r.aig)

theorem vzip_ok (func : (aig : AIG Nat) → BinaryInput aig → Entrypoint Nat) [LawfulOperator Nat BinaryInput func]
    [RefVec.LawfulZipOperator Nat func] (op : Bool → Bool → Bool) (vop : BitVec w → BitVec w → BitVec w)
    (hf : ∀ (aig : AIG Nat) (input : BinaryInput aig) (assign : Nat → Bool),
      ⟦func aig input, assign⟧ = op ⟦aig, input.lhs, assign⟧ ⟦aig, input.rhs, assign⟧)
    (hv : ∀ (x y : BitVec w) i, (vop x y).getLsbD i = (decide (i < w) && op (x.getLsbD i) (y.getLsbD i)))
    {aig : AIG Nat} {assign : Nat → Bool} {a b : Bits} {x y : BitVec w}
    (ha : Denotes aig assign a x) (hb : Denotes aig assign b y) :
    Yields aig assign (vzip func a b w aig) (vop x y) := by
  obtain ⟨va, hva, hda⟩ := toVec_of_denotes ha
  obtain ⟨vb, hvb, hdb⟩ := toVec_of_denotes hb
  let input : BinaryRefVec aig w := ⟨va, vb⟩
  refine ⟨(RefVec.zip aig input func).vec.refs.toArray, (RefVec.zip aig input func).aig,
    by simp [vzip, hva, hvb]; exact ⟨rfl, rfl⟩, RefVec.IsPrefix_zip input func, ?_⟩
  refine ⟨(RefVec.zip aig input func).vec, rfl, fun idx hidx => ?_⟩
  rw [RefVec.denote_zip, hf, hv]
  simp only [hidx, decide_true, Bool.true_and]
  rw [← hda idx hidx, ← hdb idx hidx]

end HDLean.Rtl.Blast
