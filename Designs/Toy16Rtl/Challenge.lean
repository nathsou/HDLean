import Designs.Toy16Rtl.Interface
import Designs.Toy16.WordProof

namespace HDLean.Toy16Rtl.Challenge
open HDLean.Rtl HDLean.Toy16 HDLean.Toy16.Word

/-- The word-level core retires like the ISA after one reset cycle, from any
power-up store (registers, register file, data memory, instance state), with the
instruction bus answered by `imem`, and reports a retirement (or has reported
the final halt) at least every two cycles. Implementation hole:
`Toy16.Word.design`. -/
theorem correctness (imem : Addr → Word) (s₀ : Store) (rst : Nat → Bool)
    (hr : rst 0 = true) (hd : ∀ t, 0 < t → rst t = false) :
    ∃ regs mem, let retire := fun t => retireAt Toy16.Word.design imem s₀ rst (t + 1)
      RetiresLike retire (isaRetire imem (ArchState.atReset regs mem)) ∧ Progress 2 retire Retire.halt :=
  correctness_impl imem s₀ rst hr hd

end HDLean.Toy16Rtl.Challenge
