import Designs.Toy16.WordRefinement

/-!
# Proof: the word-level Toy16 retires like the ISA

The core is the two-module design `Toy16.Word.design` (an ALU and the core,
with the register file and data memory as RTL memories). Its instruction bus
is answered by the program `imem` at the fetch address (`loop`). After one
reset cycle, from any power-up store, the retirement reports on its outputs
are exactly the ISA's retirement stream from some initial register and memory
contents, and a report (or the final halt report) appears at least every two
cycles.
-/
namespace HDLean.Toy16.Word
open HDLean.Rtl HDLean.Rtl.Build

theorem correctness_impl (imem : Addr → Word) (s₀ : Store) (rst : Nat → Bool)
    (hr : rst 0 = true) (hd : ∀ t, 0 < t → rst t = false) :
    ∃ regs mem, let retire := fun t => retireAt design imem s₀ rst (t + 1)
      RetiresLike retire (isaRetire imem (ArchState.atReset regs mem)) ∧ Progress 2 retire Retire.halt := by
  have hloop : loop design imem = ⟨id, fun st r => design.step st (fetch imem st, r)⟩ := by
    simp only [loop, fetchOut_eq]
  let s1 := (loop design imem).stateFrom s₀ rst 1
  let impl : Machine Store Unit (Option Retire) :=
    ⟨s1, fun s => observeRegs (regsOfStore s), fun s _ => design.step s (fetch imem s, false)⟩
  let xs : Nat → Unit := fun _ => ()
  have hstate : ∀ t, impl.stateAt xs t = (loop design imem).stateFrom s₀ rst (t + 1) := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Machine.stateAt_succ, ih, PMachine.stateFrom_succ (t := t + 1), hd (t + 1) (by omega), hloop]
  have hrun : (fun t => retireAt design imem s₀ rst (t + 1)) = impl.run xs := by
    funext t
    simp only [retireAt, Machine.run, outputsOf_eq, hstate]
    rfl
  have hs1 := reset_regs s₀ (fetch imem s₀)
  have hs1' : s1 = design.step s₀ (fetch imem s₀, true) := by
    show design.step s₀ (fetchOut design imem s₀, rst 0) = _; rw [hr, fetchOut_eq]
  refine ⟨s1.mem 0 3 16, s1.mem 1 8 16, ?_⟩
  intro retire
  show RetiresLike (fun t => retireAt design imem s₀ rst (t + 1)) _ ∧ Progress 2 (fun t => retireAt design imem s₀ rst (t + 1)) _
  rw [hrun]
  constructor
  · apply retiresLike_of_simulation impl (step imem) _ (effect imem) (Rel imem)
    · refine Or.inl ⟨by show (regsOfStore s1).valid.getLsbD 0 = false; rw [hs1']; exact hs1.2.2, ArchState.ext' ?_ rfl rfl ?_⟩
      · show (regsOfStore s1).pc = 0; rw [hs1']; exact hs1.1
      · show (regsOfStore s1).halted.getLsbD 0 = false; rw [hs1']; exact hs1.2.1
    · intro s q _ hR hout
      rcases hR with ⟨-, hq⟩ | ⟨-, -, hobs, -⟩
      · exact rel_next imem s q hq
      · exact absurd (hobs.symm.trans hout) (by simp)
    · intro s q _ a hR hout
      rcases hR with ⟨hv, -⟩ | ⟨-, hl, hobs, hq⟩
      · exact absurd ((observe_none hv).symm.trans hout) (by simp)
      · refine ⟨Option.some.inj (hout.symm.trans hobs), ?_⟩
        have : step imem q = archOf s := by simp only [step, hl, Bool.false_eq_true, ite_false]; exact hq.symm
        rw [this]
        exact rel_next imem s _ rfl
  · -- progress, from the control registers only
    let S := impl.stateAt xs
    let V := fun t => (regsOfStore (S t)).valid.getLsbD 0
    let H := fun t => (regsOfStore (S t)).halted.getLsbD 0
    have hS : ∀ t, S (t + 1) = design.step (S t) (fetch imem (S t), false) := fun t => rfl
    have hV : ∀ t, V (t + 1) = !H t := fun t => by simp only [V, H, hS]; exact next_valid imem _
    have hH0 : H 0 = false := by show (regsOfStore s1).halted.getLsbD 0 = false; rw [hs1']; exact hs1.2.1
    have hV0 : V 0 = false := by show (regsOfStore s1).valid.getLsbD 0 = false; rw [hs1']; exact hs1.2.2
    have hsome : ∀ t, (impl.run xs t).isSome = V t := by
      intro t
      show (observeRegs (regsOfStore (S t))).isSome = _
      unfold observeRegs; split <;> simp_all [V]
    have hinv : ∀ t, V t = true → H t = (regsOfStore (S t)).rhalt.getLsbD 0 := by
      intro t
      cases t with
      | zero => intro h; rw [hV0] at h; cases h
      | succ t =>
        intro h
        rw [hV] at h
        have h' : H t = false := by simpa using h
        simp only [H, hS]
        rw [next_halted, next_rhalt]
        have : (regsOfStore (S t)).halted.getLsbD 0 = false := h'
        rw [this, Bool.false_or]
    have hhist : ∀ t, V t = false → H t = true → ∃ u a, u < t ∧ impl.run xs u = some a ∧ a.halt = true := by
      intro t
      induction t with
      | zero => intro _ h; rw [hH0] at h; cases h
      | succ t ih =>
        intro hv _
        rw [hV] at hv
        have hHt : H t = true := by simpa using hv
        cases hvt : V t
        · obtain ⟨u, a, hu, ha, hh⟩ := ih hvt hHt
          exact ⟨u, a, by omega, ha, hh⟩
        · have hrh := hinv t hvt
          let r := regsOfStore (S t)
          refine ⟨t, Retire.mk r.rpc r.rinstr r.rnext (if r.wbv.getLsbD 0 then some (r.wbr, r.wbval) else none)
            (if r.stv.getLsbD 0 then some (r.sta, r.stval) else none) (r.rhalt.getLsbD 0), by omega, ?_, ?_⟩
          · show observeRegs (regsOfStore (S t)) = some _
            unfold observeRegs
            rw [if_pos hvt]
          · show (regsOfStore (S t)).rhalt.getLsbD 0 = true
            rw [← hrh]; exact hHt
    intro t
    cases hvt : V t
    · cases hht : H t
      · refine Or.inl ⟨t + 1, by omega, by omega, ?_⟩
        rw [hsome, hV, hht]; rfl
      · obtain ⟨u, a, hu, ha, hh⟩ := hhist t hvt hht
        exact Or.inr ⟨u, a, hu, ha, hh⟩
    · exact Or.inl ⟨t, Nat.le_refl t, by omega, by rw [hsome]; exact hvt⟩

end HDLean.Toy16.Word
