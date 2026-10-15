import HDLean.Core.Expr
import Std.Tactic.BVDecide
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

/-- Fixed-width examples use the explicitly reported native bit-blasting trust level. -/
theorem gray_one_bit8 (x : BitVec 8) :
    let d := gray x ^^^ gray (x + 1)
    d ≠ 0 ∧ d &&& (d - 1) = 0 := by
  simp only [gray]
  bv_decide

theorem one_bit_mix8 (a b m : BitVec 8) (h : (a ^^^ b) &&& ((a ^^^ b) - 1) = 0) :
    sampleBits a b m = a ∨ sampleBits a b m = b := by
  simp only [sampleBits]
  bv_decide

example : sampleBits (7 : BitVec 4) 8 7 = 15 := by decide
end HDLean
