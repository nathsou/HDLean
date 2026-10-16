import Designs.Toy16.DagRefinement
namespace HDLean.Toy16.Challenge
open DagPhysical

/-- The emitted CPU's retirement bus refines the ISA after one reset cycle, for
arbitrary power-up register and data-memory contents. The two-cycle progress bound
rejects a core that stalls. Implementation hole: `DagPhysical.hardware`. -/
theorem correctness (imem : Addr → Word) (s₀ : Fin (268*16) → Bool) (rst : Nat → Bool)
    (hr : rst 0 = true) (hd : ∀ t, 0 < t → rst t = false) :
    ∃ regs mem,
      let retire := fun t => Physical.observe (((hardware imem).denote (Dag.isMoore_of_no_inputs _)).runFrom
        s₀ (fun n => (Fin.elim0, rst n)) (t+1))
      RetiresLike retire (isaRetire imem (ArchState.atReset regs mem)) ∧ Progress 2 retire Retire.halt :=
  hardware_correct_denote imem s₀ rst hr hd

/-- Data memory, registers, fetch/control state and padding. -/
theorem budget (imem : Addr → Word) : (hardware imem).ffBits ≤ 4288 := Nat.le_refl _

end HDLean.Toy16.Challenge
