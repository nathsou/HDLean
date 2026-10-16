import HDLean.Semantics.Clock
import Init.Data.BitVec.Bitblast
namespace HDLean

theorem increment_bit (x : BitVec w) (i : Nat) (hi : i < w) :
    (x + 1).getLsbD i = (x.getLsbD i ^^ decide (∀ j < i, x.getLsbD j = true)) := by
  rw [BitVec.getLsbD_add hi]
  cases i with
  | zero => simp [hi]
  | succ i =>
    have hc : BitVec.carry (i+1) x (1 : BitVec w) false = decide (∀ j ≤ i, x.getLsbD j = true) := by
      exact BitVec.carry_succ_one i x (by omega)
    rw [hc]
    have hone : (1 : BitVec w).getLsbD (i+1) = false := by simp
    rw [hone]
    simp only [Bool.false_bne, Nat.lt_add_one_iff]

theorem first_false_or_all (f : Nat → Bool) (w : Nat) :
    (∀ j < w, f j = true) ∨ ∃ k < w, f k = false ∧ ∀ j < k, f j = true := by
  induction w with
  | zero => left; intro j hj; omega
  | succ w ih =>
    rcases ih with ha | ⟨k, hk, hf, hb⟩
    · cases hf : f w with
      | false => right; exact ⟨w, by omega, hf, ha⟩
      | true => left; intro j hj; by_cases he : j = w; simpa [he] using hf; exact ha j (by omega)
    · right; exact ⟨k, by omega, hf, hb⟩

theorem gray_adjacent (x : BitVec w) (hw : 0 < w) : Adjacent (gray x) (gray (x + 1)) := by
  rcases first_false_or_all x.getLsbD w with ha | ⟨k, hk, hf, hb⟩
  · refine ⟨⟨w - 1, by omega⟩, ?_⟩
    intro j hj
    have hjv : j.val ≠ w - 1 := by intro he; exact hj (Fin.ext he)
    have hj1 : j.val + 1 < w := by omega
    have hp : ∀ t < j.val, x.getLsbD t = true := fun t ht => ha t (by omega)
    have hp1 : ∀ t < j.val + 1, x.getLsbD t = true := fun t ht => ha t (by omega)
    simp only [gray, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, Nat.add_comm 1]
    rw [increment_bit x j.val j.isLt, increment_bit x (j.val+1) hj1]
    rw [show decide (∀ t < j.val, x.getLsbD t = true) = true from decide_eq_true hp,
      show decide (∀ t < j.val + 1, x.getLsbD t = true) = true from decide_eq_true hp1]
    simp
  · refine ⟨⟨k, hk⟩, ?_⟩
    intro j hj
    have hjk : j.val ≠ k := by intro he; exact hj (Fin.ext he)
    simp only [gray, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, Nat.add_comm 1]
    by_cases hlt : j.val < k
    · have hj1 : j.val + 1 < w := by omega
      have hp : ∀ t < j.val, x.getLsbD t = true := fun t ht => hb t (by omega)
      have hp1 : ∀ t < j.val + 1, x.getLsbD t = true := fun t ht => hb t (by omega)
      rw [increment_bit x j.val j.isLt, increment_bit x (j.val+1) hj1]
      rw [show decide (∀ t < j.val, x.getLsbD t = true) = true from decide_eq_true hp,
        show decide (∀ t < j.val + 1, x.getLsbD t = true) = true from decide_eq_true hp1]
      simp
    · have hp : ¬ (∀ t < j.val, x.getLsbD t = true) := by
        intro hh; have := hh k (by omega); simp [hf] at this
      rw [increment_bit x j.val j.isLt]
      by_cases hj1 : j.val + 1 < w
      · have hp1 : ¬ (∀ t < j.val + 1, x.getLsbD t = true) := by
          intro hh; have := hh k (by omega); simp [hf] at this
        rw [increment_bit x (j.val+1) hj1]
        simp [hp, hp1]
      · rw [BitVec.getLsbD_of_ge x (j.val+1) (by omega), BitVec.getLsbD_of_ge (x+1) (j.val+1) (by omega)]
        simp [hp]

/-- Gray encoding is injective at every width. -/
theorem gray_injective (a b : BitVec w) (h : gray a = gray b) : a = b := by
  have bits : ∀ n i, w - i = n → a.getLsbD i = b.getLsbD i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      rw [BitVec.getLsbD_of_ge a i (by omega), BitVec.getLsbD_of_ge b i (by omega)]
    | succ n ih =>
      intro i hi
      have hn := ih (i + 1) (by omega)
      have he := congrArg (fun x : BitVec w => x.getLsbD i) h
      simp only [gray, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, Nat.add_comm 1, hn] at he
      exact Bool.xor_left_inj.mp he
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact bits (w-i) i rfl

/-- Positive-width Gray increments really change their unique possible bit. -/
theorem gray_increment_ne (x : BitVec w) (hw : 0 < w) : gray x ≠ gray (x + 1) := by
  intro he
  have hx := (gray_injective x (x + 1) he).symm
  have hone := BitVec.add_right_eq_self.mp hx
  have ht := congrArg BitVec.toNat hone
  simp [BitVec.toNat_ofNat, Nat.one_mod_two_pow hw] at ht

/-- Every metastable sample between successive Gray words is one of its endpoints. -/
theorem sample_gray_increment (x mask : BitVec w) (hw : 0 < w) :
    sampleBits (gray x) (gray (x + 1)) mask = gray x ∨
    sampleBits (gray x) (gray (x + 1)) mask = gray (x + 1) :=
  sample_adjacent _ _ _ (gray_adjacent x hw)

end HDLean
