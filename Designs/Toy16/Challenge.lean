import Designs.Toy16.Core
namespace HDLean.Toy16.Challenge
/-- Reset does not invent initial register or memory contents; progress excludes a stalled core. -/
theorem correctness (imem : Addr → Word) (s₀ : CoreState) (rst : Nat → Bool)
    (hr : rst 0 = true) (hd : ∀ t, 0 < t → rst t = false) :
    ∃ regs mem,
      let retire := fun t => (core imem).runFrom s₀ rst (t + 1)
      RetiresLike retire (isaRetire imem (ArchState.atReset regs mem)) ∧
      Progress 2 retire Retire.halt := core_correct imem s₀ rst hr hd
end HDLean.Toy16.Challenge
