import HDLean.Core.Expr
import Init.Data.BitVec.Bitblast
import Init.Data.Nat.Power2.Bitwise
namespace HDLean

/-- Each global step carries independent edges, chosen by the environment. -/
structure ClockOracle where
  edge : Domain → Bool
  sampleNew : Domain → Nat → Bool

/-- A signal cannot change domains by coercion. -/
structure Signal (domain : Domain) (α : Type) where
  value : α

/-- Per-bit metastable sampling chooses old or new independently. -/
def sampleBits (old new mask : BitVec w) : BitVec w := (old &&& mask) ||| (new &&& ~~~mask)

def gray (x : BitVec w) : BitVec w := x ^^^ (x >>> 1)

/-- Being Gray-encoded is insufficient alone: a crossing also needs an adjacency proof. -/
def Adjacent (a b : BitVec w) : Prop :=
  ∃ k : Fin w, ∀ j : Fin w, j ≠ k → a.getLsbD j.val = b.getLsbD j.val

/-- Any per-bit mixture of adjacent words is one endpoint, for every width (kernel-only). -/
theorem sample_adjacent (a b m : BitVec w) (h : Adjacent a b) :
    sampleBits a b m = a ∨ sampleBits a b m = b := by
  obtain ⟨k, hk⟩ := h
  by_cases hm : m.getLsbD k.val = true
  · left
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    by_cases he : j = k.val
    · subst j
      simp only [sampleBits, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hm]
      simp
    · have he' : (⟨j, hj⟩ : Fin w) ≠ k := by intro h; exact he (congrArg Fin.val h)
      have hab := hk ⟨j,hj⟩ he'
      simp only [sampleBits, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not]
      rw [hab]
      cases b.getLsbD j <;> cases m.getLsbD j <;> simp [hj]
  · right
    have hm' : m.getLsbD k.val = false := by simpa using hm
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    by_cases he : j = k.val
    · subst j
      simp only [sampleBits, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hm']
      simp [k.isLt]
    · have he' : (⟨j, hj⟩ : Fin w) ≠ k := by intro h; exact he (congrArg Fin.val h)
      have hab := hk ⟨j,hj⟩ he'
      simp only [sampleBits, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not]
      rw [hab]
      cases b.getLsbD j <;> cases m.getLsbD j <;> simp [hj]

/-- One named physical assumption accompanies synchronizer reports; it is not an axiom proving logic. -/
def metastabilityAssumption : String := "Two-flop synchronizers resolve metastability before the second sampling edge."

structure Sync2 (α : Type) where
  first : α
  second : α
  deriving Repr, BEq

/-- The second flop samples the OLD first flop on a destination edge. -/
def sync2Step (s : Sync2 Bool) (edge old new late : Bool) : Sync2 Bool :=
  if edge then ⟨if late then new else old, s.first⟩ else s

theorem sync2_no_edge (s : Sync2 Bool) (a b m : Bool) : sync2Step s false a b m = s := rfl

/-- Two destination edges with stable source deliver that source, for every sampling oracle. -/
theorem sync2_stable (s : Sync2 Bool) (v a b : Bool) :
    (sync2Step (sync2Step s true v v a) true v v b).second = v := by
  cases a <;> cases b <;> rfl

/-- The only generic crossing exposed for raw data is a single bit. -/
def crossBit (s : Sync2 Bool) (sourceOld sourceNew : Signal a Bool)
    (oracle : ClockOracle) (dest : Domain) : Sync2 Bool × Signal dest Bool :=
  let s' := sync2Step s (oracle.edge dest) sourceOld.value sourceNew.value (oracle.sampleNew dest 0)
  (s', ⟨s'.second⟩)


/-- A single differing bit gives the relational adjacency needed by the sampler. -/
theorem adjacent_of_xor_twoPow (a b : BitVec w) (k : Fin w)
    (h : a ^^^ b = BitVec.twoPow w k.val) : Adjacent a b := by
  refine ⟨k, ?_⟩
  intro j hj
  have hne : k.val ≠ j.val := by
    intro he
    exact hj (Fin.ext he.symm)
  have hb := congrArg (fun x : BitVec w => x.getLsbD j.val) h
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_twoPow] at hb
  simp [hne] at hb
  exact hb

/-- The standard bit trick detects zero or one set bit at every width. -/
theorem eq_zero_or_twoPow_of_and_pred_eq_zero (d : BitVec w)
    (h : d &&& (d - 1) = 0) : d = 0 ∨ ∃ k : Fin w, d = BitVec.twoPow w k.val := by
  by_cases hz : d = 0
  · exact Or.inl hz
  right
  have hn : d.toNat ≠ 0 := by
    intro he
    apply hz
    apply BitVec.eq_of_toNat_eq
    simpa using he
  have hw : 0 < w := by
    have := d.isLt
    cases w with
    | zero => simp at this; omega
    | succ n => omega
  have hone : (1 : BitVec w).toNat = 1 := by simp [BitVec.toNat_ofNat, Nat.one_mod_two_pow hw]
  have hle : (1 : BitVec w) ≤ d := by rw [BitVec.le_def, hone]; omega
  have hd := congrArg BitVec.toNat h
  simp only [BitVec.toNat_and, BitVec.toNat_sub_of_le hle, hone] at hd
  obtain ⟨k, hk⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hn).mp hd
  have hkw : k < w := by
    have := d.isLt
    rw [hk] at this
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  refine ⟨⟨k, hkw⟩, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simpa [BitVec.toNat_twoPow_of_lt hkw] using hk

/-- Width-generic, kernel-only version of the bit-mixture safety theorem. -/
theorem one_bit_mix (a b m : BitVec w) (h : (a ^^^ b) &&& ((a ^^^ b) - 1) = 0) :
    sampleBits a b m = a ∨ sampleBits a b m = b := by
  rcases eq_zero_or_twoPow_of_and_pred_eq_zero (a ^^^ b) h with hz | ⟨k, hk⟩
  · have hab : a = b := BitVec.xor_eq_zero_iff.mp hz
    subst b
    left
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [sampleBits, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not]
    cases a.getLsbD j <;> cases m.getLsbD j <;> simp [hj]
  · exact sample_adjacent a b m (adjacent_of_xor_twoPow a b k hk)

/-- Exhaustive eight-bit adjacency certificate, replayable by the kernel and nanoda. -/
theorem gray_one_bit8_kernel : ∀ x : BitVec 8,
    let d := gray x ^^^ gray (x + 1)
    d ≠ 0 ∧ d &&& (d - 1) = 0 := by
  decide +kernel


/-- Fixed-width Gray adjacency certificate, checked in the kernel. -/
theorem gray_one_bit8 (x : BitVec 8) :
    let d := gray x ^^^ gray (x + 1)
    d ≠ 0 ∧ d &&& (d - 1) = 0 := by
  exact gray_one_bit8_kernel x

theorem one_bit_mix8 (a b m : BitVec 8) (h : (a ^^^ b) &&& ((a ^^^ b) - 1) = 0) :
    sampleBits a b m = a ∨ sampleBits a b m = b := by
  exact one_bit_mix a b m h

example : sampleBits (7 : BitVec 4) 8 7 = 15 := by decide
end HDLean
