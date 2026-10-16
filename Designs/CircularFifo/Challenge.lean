import Designs.Fifo.CircularRefinement
namespace HDLean.Fifo.Circular.Challenge

/-- From any power-up state, after one reset cycle, the general-depth FIFO follows
the reviewed bounded queue of capacity 2^k, for every depth exponent and payload
width. Implementation holes: `Physical.hardware`, `Physical.hardware_moore`. -/
theorem correctness (k w : Nat) :
    RefinesAfterReset ((Physical.hardware k w).denote (Physical.hardware_moore k w))
      (Reference.queueSpec k w) Reference.observe 1 :=
  Physical.hardware_refines_reference k w

/-- Two control words plus 2^k storage words, each `max (k+1) w` bits wide. -/
theorem budget (k w : Nat) : (Physical.hardware k w).ffBits ≤ (2+2^k) * max (k+1) w :=
  Nat.le_of_eq (Physical.storage_bits k w)

end HDLean.Fifo.Circular.Challenge
