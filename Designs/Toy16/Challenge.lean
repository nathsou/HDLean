import Designs.Toy16.Hardware
namespace HDLean.Toy16.Challenge
/-- The emitted physical retirement bus refines the ISA after reset, for arbitrary
power-up register and data-memory contents. The two-cycle progress bound rejects stalling. -/
theorem correctness (imem : Addr → Word) (s₀ : Fin (268*16) → Bool) (rst : Nat → Bool)
    (hr : rst 0 = true) (hd : ∀ t, 0 < t → rst t = false) :
    ∃ regs mem,
      let retire := fun t => Physical.observe (((Physical.hardware imem).denote
        (Physical.hardware_moore imem)).runFrom s₀ (fun n => (Fin.elim0,rst n)) (t+1))
      RetiresLike retire (isaRetire imem (ArchState.atReset regs mem)) ∧ Progress 2 retire Retire.halt :=
  Physical.hardware_correct imem s₀ rst hr hd

/-- Includes data memory, registers, fetch/control state and all padding. -/
theorem budget (imem : Addr → Word) : (lower (Physical.hardware imem)).ffBits ≤ 4288 := by
  rw [Physical.ffBits]
  exact Nat.le_refl _
end HDLean.Toy16.Challenge
