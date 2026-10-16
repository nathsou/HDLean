import HDLean.Rtl.Syntax

/-! Structural lemmas about well-formedness, used by the builder. -/
namespace HDLean.Rtl

theorem cellsValidFrom_append (sc : Scope) (ws : Array Nat) (xs ys : List Cell) :
    cellsValidFrom sc ws (xs ++ ys) =
      (cellsValidFrom sc ws xs && cellsValidFrom sc (ws ++ (xs.map Cell.width).toArray) ys) := by
  induction xs generalizing ws with
  | nil => simp [cellsValidFrom]
  | cons c cs ih =>
    simp only [List.cons_append, cellsValidFrom, ih, Bool.and_assoc, List.map_cons]
    congr 3
    simp

theorem cellsValid_push (sc : Scope) (cells : Array Cell) (c : Cell) :
    cellsValid sc (cells.push c) =
      (cellsValid sc cells && (0 < c.width && c.op.valid sc (cells.map Cell.width) c.width)) := by
  simp only [cellsValid, Array.toList_push, cellsValidFrom_append, cellsValidFrom, Bool.and_true]
  congr 3
  apply Array.ext'
  simp

/-- A scope with more registers or memories accepts every cell it accepted. -/
structure Scope.Le (a b : Scope) : Prop where
  inputs : a.inputs = b.inputs
  subs : a.subs = b.subs
  regs : ∀ (k v : Nat), a.regs[k]? = some v → b.regs[k]? = some v
  mems : ∀ (k : Nat) (v : Nat × Nat), a.mems[k]? = some v → b.mems[k]? = some v

theorem Op.valid_mono {sa sb : Scope} (h : sa.Le sb) {ws : Array Nat} {w : Nat} :
    ∀ op : Op, op.valid sa ws w = true → op.valid sb ws w = true := by
  intro op hv
  cases op with
  | input k => rw [Op.valid, ← h.inputs]; exact hv
  | reg k =>
    simp only [Op.valid, beq_iff_eq] at hv ⊢
    exact h.regs _ _ hv
  | memRead mi x =>
    simp only [Op.valid] at hv ⊢
    cases hm : sa.mems[mi]? with
    | none => simp [hm] at hv
    | some p => rw [h.mems _ _ hm]; simpa [hm] using hv
  | inst j args outs => rw [Op.valid, ← h.subs]; exact hv
  | _ => simpa [Op.valid] using hv

theorem cellsValidFrom_mono {a b : Scope} (h : a.Le b) :
    ∀ (cs : List Cell) (ws : Array Nat), cellsValidFrom a ws cs = true → cellsValidFrom b ws cs = true
  | [], _, _ => rfl
  | c :: cs, ws, hv => by
    simp only [cellsValidFrom, Bool.and_eq_true] at hv ⊢
    exact ⟨⟨hv.1.1, Op.valid_mono h _ hv.1.2⟩, cellsValidFrom_mono h cs _ hv.2⟩

theorem cellsValid_mono {a b : Scope} (h : a.Le b) (cells : Array Cell) :
    cellsValid a cells = true → cellsValid b cells = true :=
  cellsValidFrom_mono h _ _

/-- Each earlier reference in a valid cell list points backwards. -/
theorem cellsValid_prefix (sc : Scope) (cells more : Array Cell) :
    cellsValid sc (cells ++ more) = true → cellsValid sc cells = true := by
  simp only [cellsValid, Array.toList_append, cellsValidFrom_append, Bool.and_eq_true]
  exact And.left

end HDLean.Rtl
