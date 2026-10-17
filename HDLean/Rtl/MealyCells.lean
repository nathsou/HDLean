import HDLean.Rtl.Memory

/-!
# Register cells of a Mealy module

Some semantics look at a module's syntax, not only at its values: a clock
domain crossing or a shared memory's read address must be driven *directly* by
a register (`MDesign.regOut`). `RegCell t x j` says that handle `x` is the cell
reading register `j`. `mealy_build_cells` hands the body these facts about the
register record it receives, so a body can return a register as an output and
prove that the output is that register.
-/
namespace HDLean.Rtl.Build

/-- Handle `x` is the cell that reads register `j`. -/
def RegCell {c : Ctx} (t : State c) (x : Sig w) (j : Nat) : Prop := t.cells[x.ref]? = some ⟨w, .reg j⟩

theorem RegCell.mono {c : Ctx} {s t : State c} {x : Sig w} {j : Nat} (h : RegCell s x j) (hx : Extends s t) :
    RegCell t x j := by
  obtain ⟨more, hm⟩ := hx
  have hl : x.ref < s.cells.size := by
    rcases Nat.lt_or_ge x.ref s.cells.size with hl | hl
    · exact hl
    · simp [RegCell, Array.getElem?_eq_none hl] at h
  unfold RegCell at h ⊢
  rw [hm, Array.getElem?_append_left hl, h]

/-- The handles of a vector read registers `base`, `base + 1`, ... -/
def HRegCells {c : Ctx} (t : State c) : {ws : List Nat} → HVec Sig ws → Nat → Prop
  | [], _, _ => True
  | _ :: _, v, base => RegCell t v.head base ∧ HRegCells t v.tail (base + 1)

theorem HRegCells.mono {c : Ctx} {s t : State c} (hx : Extends s t) :
    ∀ {ws : List Nat} {v : HVec Sig ws} {base : Nat}, HRegCells s v base → HRegCells t v base
  | [], _, _, _ => trivial
  | _ :: _, _, _, h => ⟨h.1.mono hx, HRegCells.mono hx h.2⟩

/-- The fields of a register record read the registers in order. -/
def BRegCells {c : Ctx} {R : (Nat → Type) → Type} [Bundle R] (t : State c) (r : R Sig) : Prop :=
  HRegCells t (Bundle.toVec r) 0

theorem BRegCells.mono {c : Ctx} {R : (Nat → Type) → Type} [Bundle R] {s t : State c} {r : R Sig}
    (h : BRegCells s r) (hx : Extends s t) : BRegCells t r :=
  HRegCells.mono hx h

/-- Two facts about one deterministic program. -/
theorem ensures_and {c : Ctx} {s : State c} {m : M c α} {p q : α → State c → Prop}
    (hp : Ensures s m p) (hq : Ensures s m q) : Ensures s m (fun a t => p a t ∧ q a t) := by
  obtain ⟨a, t, hm, he, ha⟩ := hp
  obtain ⟨a', t', hm', -, ha'⟩ := hq
  rw [hm] at hm'
  cases hm'
  exact ⟨a, t, hm, he, ha, ha'⟩

theorem regRead_cell (s : State c) (k w : Nat) (hw : 0 < w)
    (hk : (c.regs[k]?).map RegSpec.width = some w) :
    Ensures s (regRead k w) (fun x t => RegCell t x k) := by
  have hv : (0 < w && Op.valid c.scope s.widths w (.reg k)) = true := by
    simp [Op.valid, hw, Ctx.scope, Array.getElem?_map, hk]
  refine ⟨⟨s.cells.size⟩, _, by simp [regRead, emit, hv]; rfl, ⟨#[⟨w, .reg k⟩], by simp⟩, ?_⟩
  show (s.cells.push ⟨w, .reg k⟩)[s.cells.size]? = some ⟨w, .reg k⟩
  simp

theorem readRegs_cells (s : State c) (ws : List Nat) (base : Nat) (hpos : ∀ w ∈ ws, 0 < w)
    (hk : ∀ (k : Nat), (c.regs[base + k]?).map RegSpec.width = ws[k]? ∨ ws.length ≤ k) :
    Ensures s (readRegs ws base) (fun v t => HRegCells t v base) := by
  induction ws generalizing s base with
  | nil => exact ensures_pure _ _ trivial
  | cons w ws ih =>
    have h0 : (c.regs[base]?).map RegSpec.width = some w := by
      rcases hk 0 with h | h
      · simpa using h
      · simp at h
    unfold readRegs
    apply ensures_bind (regRead_cell _ base w (hpos w (by simp)) h0)
    intro x t ext hx
    apply ensures_bind (ih _ (base + 1) (fun v hv => hpos v (by simp [hv]))
      (fun k => by rcases hk (k + 1) with h | h
                   · left; simpa [Nat.add_assoc, Nat.add_comm 1 k] using h
                   · right; simp at h; omega))
    intro xs t' ext' hxs
    exact ensures_pure _ _ ⟨hx.mono ext', hxs⟩

theorem mealy_ensures_cells (I O R : (Nat → Type) → Type) [Bundle I] [Bundle O] [Bundle R]
    (body : I Sig → R Sig → M c (Step O R)) (post : Step O R → State c → Prop)
    (hI : ∀ (k : Nat), (c.inputs[k]?).map Port.width = (Bundle.widths I)[k]? ∨ (Bundle.widths I).length ≤ k)
    (hR : ∀ (k : Nat), (c.regs[k]?).map RegSpec.width = (Bundle.widths R)[k]? ∨ (Bundle.widths R).length ≤ k)
    (hposI : ∀ w ∈ Bundle.widths I, 0 < w) (hposR : ∀ w ∈ Bundle.widths R, 0 < w)
    (hbody : ∀ s ins regs, BRefines s ins (fun e => Bundle.decode I (e.ins.getD · 0)) →
      BRefines s regs (fun e => Bundle.decode R (e.st.regs.getD · 0)) → BRegCells s regs →
      Ensures s (body ins regs) post) :
    Ensures (init c) (mealy I O R body) (fun r t => ∃ st, post st t ∧
      r = ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩) := by
  unfold mealy
  apply ensures_bind (readInputs_ensures _ _ 0 hposI (by simpa using hI))
  intro ins t1 e1 hins
  apply ensures_bind (ensures_and (readRegs_ensures _ _ 0 hposR (by simpa using hR))
    (readRegs_cells _ _ 0 hposR (by simpa using hR)))
  intro regs t2 e2 ⟨hregs, hcells⟩
  have hins' : BRefines t2 (Bundle.ofVec ins : I Sig) (fun e => Bundle.decode I (e.ins.getD · 0)) := by
    unfold BRefines Bundle.decode; simpa [Bundle.toVec_ofVec] using hins.mono e2
  have hregs' : BRefines t2 (Bundle.ofVec regs : R Sig) (fun e => Bundle.decode R (e.st.regs.getD · 0)) := by
    unfold BRefines Bundle.decode; simpa [Bundle.toVec_ofVec] using hregs
  have hcells' : BRegCells t2 (Bundle.ofVec regs : R Sig) := by
    unfold BRegCells; simpa [Bundle.toVec_ofVec] using hcells
  apply ensures_bind (hbody t2 _ _ hins' hregs' hcells')
  intro st t3 e3 hpost
  exact ensures_pure _ _ ⟨st, hpost, rfl⟩

section
variable {name : String} {I O R : (Nat → Type) → Type} [Bundle I] [Bundle O] [Bundle R]
  {resets : R (fun _ => Reset)} {mems : Array MemSpec} {subs : Array (List Nat × List Nat)}

/-- `mealy_build_with` where the body also knows which register each field of
its register record reads. -/
theorem mealy_build_cells (hc : (Ctx.mealy name I O R resets mems subs).ok = true)
    (body : I Sig → R Sig → M (Ctx.mealy name I O R resets mems subs) (Step O R))
    (specO : Env → O BitVec) (specR : Env → R BitVec)
    (P : Step O R → State (Ctx.mealy name I O R resets mems subs) → Prop)
    (hbody : ∀ s ins regs, BRefines s ins (fun e => Bundle.decode I (e.ins.getD · 0)) →
      BRefines s regs (fun e => Bundle.decode R (e.st.regs.getD · 0)) → BRegCells s regs →
      Ensures s (body ins regs) (fun st t => BRefines t st.out specO ∧ BRefines t st.next specR ∧
        WritesOk t st.writes mems ∧ P st t)) :
    ∃ (t : State (Ctx.mealy name I O R resets mems subs)) (st : Step O R),
      (Ctx.mealy name I O R resets mems subs).module (mealy I O R body) =
        t.toModule ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩ ∧
      BRefines t st.out specO ∧ BRefines t st.next specR ∧ WritesOk t st.writes mems ∧ P st t := by
  obtain ⟨hpI, hpR⟩ := Ctx.mealy_ok_pos hc
  obtain ⟨r, t, hp, -, st, hpost, rfl⟩ := mealy_ensures_cells I O R body _
    Ctx.mealy_input_widths Ctx.mealy_reg_widths hpI hpR hbody
  exact ⟨t, st, Ctx.module_eq hp hc (mealy_wired t st hpost.1 hpost.2.1 hpost.2.2.1.1 hpost.2.2.1.2),
    hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2⟩

end

/-- Output `o` of a finished module is the handle the body returned for it. -/
theorem State.toModule_output {c : Ctx} (t : State c) (r : Wiring) (o : Nat) (n : Nat)
    (hn : r.outputs[o]? = some n) (ho : o < c.outputs.size) :
    ((t.toModule r).outputs[o]?).map OutPort.node = some n := by
  simp only [State.toModule, Array.getElem?_map]
  have hl : o < r.outputs.size := by
    rcases Nat.lt_or_ge o r.outputs.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hn
  rw [Array.getElem?_eq_getElem (by simp [Array.size_zip]; omega)]
  simp only [Option.map_some, Array.getElem_zip]
  rw [Array.getElem?_eq_getElem hl] at hn
  simpa using hn

theorem State.toModule_cells {c : Ctx} (t : State c) (r : Wiring) : (t.toModule r).cells = t.cells := rfl

end HDLean.Rtl.Build
