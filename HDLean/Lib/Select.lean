import HDLean.Lib.MemoryCircuit

namespace HDLean.WordExpr

/-- A balanced read mux has address-width depth rather than table-depth depth. -/
def selectBalanced : {a : Nat} → WordExpr d i r a →
    (Fin (2^a) → WordExpr d i r w) → WordExpr d i r w
  | 0, _, table => table ⟨0, by decide⟩
  | a+1, address, table =>
    let low := extract address 0 a (by omega)
    mux address[a] (selectBalanced low fun j => table ⟨2^a+j.val, by
      have := j.isLt; simp only [Nat.pow_succ, Nat.mul_two]; omega⟩)
      (selectBalanced low fun j => table ⟨j.val, by
        have := j.isLt; simp only [Nat.pow_succ, Nat.mul_two]; omega⟩)

@[simp] theorem selectBalanced_correct (address : WordExpr d i r a)
    (table : Fin (2^a) → WordExpr d i r w) (xs state) :
    (selectBalanced address table).eval xs state =
      (table ⟨(address.eval xs state).toNat, (address.eval xs state).isLt⟩).eval xs state := by
  induction a with
  | zero =>
    simp only [selectBalanced]
    congr 2
    apply Fin.ext
    have := (address.eval xs state).isLt
    simp at this
    exact this.symm
  | succ a ih =>
    simp only [selectBalanced, eval_mux, ih]
    have hbit : address[a].eval xs state = decide (2^a ≤ (address.eval xs state).toNat) := by
      rw [← eval_bit address xs state a (by omega)]
      simpa [BitVec.msb_eq_getLsbD_last] using BitVec.msb_eq_decide (address.eval xs state)
    rw [hbit]
    have hn := (address.eval xs state).isLt
    have hp : 0 < 2^a := Nat.two_pow_pos a
    simp only [Nat.pow_succ, Nat.mul_two] at hn
    split
    · rename_i hge
      simp only [decide_eq_true_eq] at hge
      have hm : (address.eval xs state).toNat % 2^a = (address.eval xs state).toNat - 2^a := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      congr 2
      apply Fin.ext
      simp [extract_correct, BitVec.extractLsb'_toNat, hm]
      omega
    · rename_i hlt
      simp only [decide_eq_true_eq, Nat.not_le] at hlt
      congr 2
      apply Fin.ext
      simp [extract_correct, BitVec.extractLsb'_toNat, Nat.mod_eq_of_lt hlt]

end HDLean.WordExpr
