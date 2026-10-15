import Designs.Fifo.Proof
namespace HDLean.Fifo.Challenge
/-- Frozen obligation: exact two-entry queue behavior after reset, for every payload width. -/
theorem correctness (w : Nat) :
    RefinesAfterReset ((hardware w).denote (hardware_moore w)) (wireSpec w) observe 1 := hardware_correct w
/-- The implementation must stay within its explicit register-storage budget. -/
theorem budget (w : Nat) : (lower (hardware w)).ffBits ≤ 2 * w + 2 := Nat.le_of_eq (hardware_ffBits w)
end HDLean.Fifo.Challenge
