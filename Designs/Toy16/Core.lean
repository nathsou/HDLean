import Designs.Toy16.Programs
namespace HDLean.Toy16

/-- A two-stage fetch/execute core. Serialization avoids forwarding and branch-flush hazards. -/
structure CoreState where
  arch : ArchState
  fetched : Word
  execute : Bool

/-- Reset does not initialize the register file or data memory. -/
def core (imem : Addr → Word) : PMachine CoreState Bool (Option Retire) where
  out s := if s.execute && !s.arch.halted then some (effectWord s.fetched s.arch) else none
  next s rst :=
    if rst then { s with arch := ArchState.atReset s.arch.regs s.arch.dmem, execute := false }
    else if s.arch.halted then s
    else if s.execute then
      { s with arch := applyEffect s.arch (effectWord s.fetched s.arch), execute := false }
    else { s with fetched := imem s.arch.pc, execute := true }

/-- The reference relation records the fetch-stage obligation explicitly. -/
def CoreRelation (imem : Addr → Word) (s : CoreState) (q : ArchState) : Prop :=
  s.arch = q ∧ (s.execute = true → s.fetched = imem q.pc)

/-- Begin after one reset edge; arbitrary payload state is retained. -/
def coreMachine (imem : Addr → Word) (regs : Reg → Word) (mem : Addr → Word) (garbage : Word) :
    Machine CoreState Unit (Option Retire) where
  init := ⟨ArchState.atReset regs mem, garbage, false⟩
  out := (core imem).out
  next s _ := (core imem).next s false

theorem core_bubble (imem : Addr → Word) (s : CoreState) (q : ArchState)
    (h : CoreRelation imem s q) (ho : (core imem).out s = none) :
    CoreRelation imem ((core imem).next s false) q := by
  obtain ⟨rfl, hf⟩ := h
  rcases s with ⟨a, f, e⟩
  cases he : a.halted <;> cases e <;> simp_all [core, CoreRelation]

theorem core_retire (imem : Addr → Word) (s : CoreState) (q : ArchState) (a : Retire)
    (h : CoreRelation imem s q) (ho : (core imem).out s = some a) :
    a = effect imem q ∧ CoreRelation imem ((core imem).next s false) (step imem q) := by
  obtain ⟨rfl, hf⟩ := h
  rcases s with ⟨q, f, e⟩
  cases he : q.halted <;> cases e <;> simp_all [core, CoreRelation, effect, step]

theorem core_retires (imem : Addr → Word) (regs : Reg → Word) (mem : Addr → Word) (garbage : Word) :
    RetiresLike ((coreMachine imem regs mem garbage).run (fun _ => ()))
      (isaRetire imem (ArchState.atReset regs mem)) := by
  apply retiresLike_of_simulation _ (step imem) _ (effect imem) (CoreRelation imem)
  · simp [CoreRelation, coreMachine]
  · intro s q _ h ho
    exact core_bubble imem s q h ho
  · intro s q _ a h ho
    exact core_retire imem s q a h ho

/-- Once halted, a halt retirement must already have occurred. -/
theorem halted_has_retired (imem : Addr → Word) (regs mem garbage) (t : Nat)
    (h : ((coreMachine imem regs mem garbage).stateAt (fun _ => ()) t).arch.halted = true) :
    ∃ u a, u < t ∧ (coreMachine imem regs mem garbage).run (fun _ => ()) u = some a ∧ a.halt = true := by
  induction t with
  | zero => simp [coreMachine, ArchState.atReset] at h
  | succ t ih =>
    let s := (coreMachine imem regs mem garbage).stateAt (fun _ => ()) t
    by_cases hh : s.arch.halted = true
    · obtain ⟨u, a, hu, ho, ha⟩ := ih hh
      exact ⟨u, a, by omega, ho, ha⟩
    · have hh' : s.arch.halted = false := by simpa using hh
      by_cases he : s.execute = true
      · refine ⟨t, effectWord s.fetched s.arch, by omega, ?_, ?_⟩
        · change (core imem).out s = _
          simp [core, he, hh']
        · change ((core imem).next s false).arch.halted = true at h
          simpa [core, he, hh', applyEffect] using h
      · have he' : s.execute = false := by simpa using he
        change ((core imem).next s false).arch.halted = true at h
        simp [core, he', hh'] at h

/-- A live core retires within two cycles; permanently stalled implementations are rejected. -/
theorem core_progress (imem : Addr → Word) (regs mem garbage) :
    Progress 2 ((coreMachine imem regs mem garbage).run (fun _ => ())) Retire.halt := by
  intro t
  let s := (coreMachine imem regs mem garbage).stateAt (fun _ => ()) t
  by_cases hh : s.arch.halted = true
  · exact Or.inr (halted_has_retired imem regs mem garbage t hh)
  · left
    have hh' : s.arch.halted = false := by simpa using hh
    by_cases he : s.execute = true
    · refine ⟨t, by omega, by omega, ?_⟩
      change ((core imem).out s).isSome = true
      simp [core, hh', he]
    · have he' : s.execute = false := by simpa using he
      refine ⟨t + 1, by omega, by omega, ?_⟩
      change ((core imem).out ((core imem).next s false)).isSome = true
      simp [core, hh', he']

private theorem after_reset_state (imem : Addr → Word) (s₀ : CoreState) (rst : Nat → Bool)
    (hr : rst 0 = true) (hd : ∀ t, 0 < t → rst t = false) (t : Nat) :
    (core imem).stateFrom s₀ rst (t + 1) =
      (coreMachine imem s₀.arch.regs s₀.arch.dmem s₀.fetched).stateAt (fun _ => ()) t := by
  induction t with
  | zero => simp [PMachine.stateFrom, core, hr, coreMachine]
  | succ t ih =>
    rw [PMachine.stateFrom_succ, ih, hd _ (by omega), Machine.stateAt_succ]
    rfl

/-- Complete reset/retirement/progress challenge, universally quantified over garbage state. -/
theorem core_correct (imem : Addr → Word) (s₀ : CoreState) (rst : Nat → Bool)
    (hr : rst 0 = true) (hd : ∀ t, 0 < t → rst t = false) :
    ∃ regs mem,
      let retire := fun t => (core imem).runFrom s₀ rst (t + 1)
      RetiresLike retire (isaRetire imem (ArchState.atReset regs mem)) ∧
      Progress 2 retire Retire.halt := by
  refine ⟨s₀.arch.regs, s₀.arch.dmem, ?_⟩
  have he : (fun t => (core imem).runFrom s₀ rst (t + 1)) =
      (coreMachine imem s₀.arch.regs s₀.arch.dmem s₀.fetched).run (fun _ => ()) := by
    funext t
    unfold PMachine.runFrom Machine.run
    rw [after_reset_state imem s₀ rst hr hd t]
    rfl
  dsimp only
  rw [he]
  exact ⟨core_retires _ _ _ _, core_progress _ _ _ _⟩

/-- A single-cycle implementation shares the ISA state and retires every live cycle. -/
def singleCycle (imem : Addr → Word) : PMachine ArchState Bool (Option Retire) where
  out s := if s.halted then none else some (effect imem s)
  next s rst := if rst then ArchState.atReset s.regs s.dmem else step imem s

end HDLean.Toy16
