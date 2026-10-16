import HDLean.Lib.Memory
import HDLean.Core.Network
import HDLean.Core.Word

namespace HDLean
namespace WordExpr

/-- A finite read port. The address width covers exactly the table's power-of-two depth. -/
def selectEntries (address : WordExpr d i r a) (table : Fin (2 ^ a) → WordExpr d i r w) :
    List (Fin (2 ^ a)) → WordExpr d i r w
  | [] => literal 0
  | k :: ks => mux (equal address (literal (BitVec.ofNat a k.val))) (table k)
      (selectEntries address table ks)

private theorem bounded_ofNat_ne (j k : Fin (2 ^ a)) (h : j ≠ k) :
    (BitVec.ofNat a j.val) ≠ BitVec.ofNat a k.val := by
  intro he
  have hn := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt k.isLt] at hn
  exact h (Fin.ext hn)

theorem selectEntries_correct (address : WordExpr d i r a) (table : Fin (2 ^ a) → WordExpr d i r w)
    (entries : List (Fin (2 ^ a))) (target : Fin (2 ^ a))
    (hmem : target ∈ entries) (xs state)
    (ha : address.eval xs state = BitVec.ofNat a target.val) :
    (selectEntries address table entries).eval xs state = (table target).eval xs state := by
  induction entries with
  | nil => simp at hmem
  | cons k ks ih =>
    by_cases he : target = k
    · subst k
      simp [selectEntries, eval_mux, equal_correct, eval_literal, ha]
    · have hm : target ∈ ks := by simpa [he] using hmem
      simp [selectEntries, eval_mux, equal_correct, eval_literal, ha, he, ih hm]

def select (address : WordExpr d i r a) (table : Fin (2 ^ a) → WordExpr d i r w) : WordExpr d i r w :=
  selectEntries address table (List.finRange (2 ^ a))

/-- All addresses are in bounds by construction, for every address width including zero. -/
theorem select_correct (address : WordExpr d i r a) (table : Fin (2 ^ a) → WordExpr d i r w) (xs state) :
    (select address table).eval xs state =
      (table ⟨(address.eval xs state).toNat, (address.eval xs state).isLt⟩).eval xs state := by
  apply selectEntries_correct
  · simp
  · simp

end WordExpr

namespace RAMCircuit

private theorem cellBound (j : Fin (2 ^ a)) : j.val * w + w ≤ 2 ^ a * w + w := by
  have h := Nat.mul_le_mul_right w (Nat.le_of_lt j.isLt)
  omega

def address (a w : Nat) : WordExpr 0 (1 + a + w) (2 ^ a * w + w) a :=
  WordExpr.inputs 1 (by omega)

def writeData (a w : Nat) : WordExpr 0 (1 + a + w) (2 ^ a * w + w) w :=
  WordExpr.inputs (1 + a) (by omega)

def cell (a w : Nat) (j : Fin (2 ^ a)) : WordExpr 0 (1 + a + w) (2 ^ a * w + w) w :=
  WordExpr.registers (j.val * w) (cellBound j)

def readRegister (a w : Nat) : WordExpr 0 (1 + a + w) (2 ^ a * w + w) w :=
  WordExpr.registers (2 ^ a * w) (by omega)

/-- One synchronous read-before-write port, implemented as an explicit register
array. All memory and read-data bits remain unreset, including at power-up. -/
def hardware (a w : Nat) : Circuit 0 (1 + a + w) (2 ^ a * w + w) w :=
  let read := WordExpr.select (address a w) (cell a w)
  { name := s!"ram_{2 ^ a}x{w}"
    state := ((Vector.ofFn fun j : Fin (2 ^ a) => Vector.ofFn fun k : Fin w =>
      { name := s!"memory_{j.val}_{k.val}"
        reset := .unreset
        next := Expr.mux (.and (.input ⟨0, by omega⟩)
          (WordExpr.equal (address a w) (WordExpr.literal (BitVec.ofNat a j.val))))
          (writeData a w)[k] (cell a w j)[k]
        source := "HDLean/Lib/MemoryCircuit.lean" } :
        Vector (Vector (Register 0 (1 + a + w) (2 ^ a * w + w)) w) (2 ^ a)).flatten).append
      (Vector.ofFn fun k : Fin w =>
        ⟨s!"read_{k.val}", .unreset, read[k], "HDLean/Lib/MemoryCircuit.lean"⟩)
    output := readRegister a w }

def decode (s : Fin (2 ^ a * w + w) → Bool) : RAMState (2 ^ a) w :=
  ⟨Vector.ofFn (fun j => (cell a w j).eval (fun _ => false) s),
    (readRegister a w).eval (fun _ => false) s⟩

def decodeInput (a w : Nat) (xs : Fin (1 + a + w) → Bool) : RAMRequest (2 ^ a) w :=
  ⟨⟨((address a w).eval xs (fun _ => false)).toNat,
      ((address a w).eval xs (fun _ => false)).isLt⟩,
    if xs ⟨0, by omega⟩ then some ((writeData a w).eval xs (fun _ => false)) else none⟩

theorem hardware_moore (a w : Nat) : (hardware a w).IsMoore := by
  intro s x y
  funext k
  simp [hardware, Circuit.evalOutput, readRegister, WordExpr.registers, Expr.eval]

/-- Register-array storage and its registered read result have no hidden state. -/
theorem hardware_ffBits (a w : Nat) : (hardware a w).ffBits = 2 ^ a * w + w := rfl

end RAMCircuit
end HDLean

namespace HDLean.WordExpr

@[simp] theorem inputs_state (offset : Nat) (h : offset + w ≤ i) (xs : Fin i → Bool)
    (s t : Fin r → Bool) :
    (inputs offset h : WordExpr d i r w).eval xs s = (inputs offset h : WordExpr d i r w).eval xs t := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [eval_bit _ _ _ k hk, eval_bit _ _ _ k hk]
  simp [inputs, Expr.eval]

@[simp] theorem registers_inputs (offset : Nat) (h : offset + w ≤ r)
    (xs ys : Fin i → Bool) (s : Fin r → Bool) :
    (registers offset h : WordExpr d i r w).eval xs s = (registers offset h : WordExpr d i r w).eval ys s := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [eval_bit _ _ _ k hk, eval_bit _ _ _ k hk]
  simp [registers, Expr.eval]

end HDLean.WordExpr

namespace HDLean.RAMCircuit

@[simp] private theorem append_left (xs : Vector α n) (ys : Vector α m) (i : Nat) (h : i < n) :
    (xs.append ys)[i] = xs[i] := Vector.getElem_append_left h

@[simp] private theorem append_right (xs : Vector α n) (ys : Vector α m) (i : Nat)
    (h : i < n + m) (hn : n ≤ i) :
    (xs.append ys)[i] = ys[i-n] := Vector.getElem_append_right h hn

private theorem cell_next_bit (a w : Nat) (j : Fin (2 ^ a)) (k : Fin w) (s xs rst) :
    (hardware a w).next s (xs, rst) (Fin.castAdd w (flatIndex j k)) =
      if xs ⟨0, by omega⟩ &&
          ((address a w).eval xs s == BitVec.ofNat a j.val) then
        ((writeData a w)[k]).eval xs s else ((cell a w j)[k]).eval xs s := by
  have h := (flatIndex j k).isLt
  simp [Circuit.next, hardware, append_left, h, Expr.eval, WordExpr.equal_correct]

theorem cell_next (a w : Nat) (j : Fin (2 ^ a)) (s xs rst) :
    (cell a w j).eval (fun _ => false) ((hardware a w).next s (xs, rst)) =
      if xs ⟨0, by omega⟩ && ((address a w).eval xs s == BitVec.ofNat a j.val) then
        (writeData a w).eval xs s else (cell a w j).eval xs s := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [WordExpr.eval_bit _ _ _ k hk]
  simp only [cell, WordExpr.registers, Vector.getElem_ofFn, Expr.eval]
  have h := cell_next_bit a w j ⟨k,hk⟩ s xs rst
  change (hardware a w).next s (xs, rst) (Fin.castAdd w (flatIndex j ⟨k,hk⟩)) = _
  rw [h]
  split <;> simp only [Fin.getElem_fin, WordExpr.eval_bit _ _ _ k hk]
  rfl

theorem read_next (a w : Nat) (s xs rst) :
    (readRegister a w).eval (fun _ => false) ((hardware a w).next s (xs, rst)) =
      ((cell a w ⟨((address a w).eval xs s).toNat, ((address a w).eval xs s).isLt⟩).eval xs s) := by
  rw [← WordExpr.select_correct]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [WordExpr.eval_bit _ _ _ k hk, WordExpr.eval_bit _ _ _ k hk]
  simp [readRegister, WordExpr.registers, Expr.eval, Circuit.next, hardware, append_right]

theorem decode_next (a w : Nat) (s xs rst) :
    decode ((hardware a w).next s (xs, rst)) = (ram (2 ^ a) w).next (decode s) (decodeInput a w xs) := by
  have ha : (address a w).eval xs s = (address a w).eval xs (fun _ => false) :=
    WordExpr.inputs_state _ _ _ _ _
  have hd : (writeData a w).eval xs s = (writeData a w).eval xs (fun _ => false) :=
    WordExpr.inputs_state _ _ _ _ _
  have hc : ∀ j, (cell a w j).eval xs s = (cell a w j).eval (fun _ => false) s :=
    fun _ => WordExpr.registers_inputs _ _ _ _ _
  cases hw : xs ⟨0, by omega⟩ <;>
    simp only [decode, ram, decodeInput, hw, Bool.false_eq_true, ↓reduceIte]
  · congr 1
    · apply Vector.ext
      intro j hj
      simp only [Vector.getElem_ofFn, cell_next, hw, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hc]
    · simp [read_next, ha, hc]
  · congr 1
    · apply Vector.ext
      intro j hj
      simp [cell_next, hw, ha, hd, hc, Vector.getElem_set]
      split
      · simp_all
      · rename_i hne
        rw [ite_eq_right]
        intro he
        exact hne (BitVec.eq_of_toNat_eq (by simpa using he))
    · simp [read_next, ha, hc]

/-- Physical read data agrees with the semantic registered result for every
power-up state; reset does not silently initialize storage. -/
theorem decode_output (a w : Nat) (s xs) :
    (WordExpr.inputs 0 (by omega) : WordExpr 0 w 0 w).eval
      ((hardware a w).evalOutput s xs) (fun k => nomatch k) = (decode s).readData := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  change _ = ((readRegister a w).eval (fun _ => false) s).getLsbD k
  rw [WordExpr.eval_bit _ _ _ k hk, WordExpr.eval_bit _ _ _ k hk]
  simp [WordExpr.inputs, Circuit.evalOutput, hardware, readRegister, WordExpr.registers, Expr.eval]

/-- All physical traces implement the synchronous read-before-write machine,
including simultaneous access and arbitrary initial memory contents. -/
theorem hardware_correct (a w : Nat) (s₀) (xs : Nat → (Fin (1+a+w) → Bool) × Bool) (t : Nat) :
    decode (((hardware a w).denote (hardware_moore a w)).stateFrom s₀ xs t) =
      (ram (2^a) w).stateFrom (decode s₀) (fun n => decodeInput a w (xs n).1) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [PMachine.stateFrom_succ]
    change decode ((hardware a w).next _ (xs t)) = _
    rw [decode_next, ih]

end HDLean.RAMCircuit
