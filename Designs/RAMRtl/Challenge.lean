import Designs.RAMRtl.Interface
import Designs.RAM.Word

namespace HDLean.RAMRtl.Challenge
open HDLean.Rtl HDLean.RAM.Word

/-- For every power-up store (memory contents and read register) there is an
initial reference RAM state such that, under any inputs and reset sequence, the
read port shows the read-before-write reference RAM's read word on every cycle.
The memory is an RTL memory, not flip-flops. Implementation hole:
`RAM.Word.design`. -/
theorem correctness (a w : Nat) (ha : 0 < a) (hw : 0 < w) (s₀ : Store) (xs : Nat → Array Nat × Bool) :
    ∃ m₀ : RAMState (2 ^ a) w, ∀ t, readWord w (RAM.Word.design a w) ((machine (RAM.Word.design a w)).stateFrom s₀ xs t) =
      (ram (2 ^ a) w).runFrom m₀ (fun n => request a w (xs n).1) t :=
  correctness_impl a w ha hw s₀ xs

end HDLean.RAMRtl.Challenge
