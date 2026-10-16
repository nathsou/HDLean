import Designs.SkidBuffer.Hardware

namespace HDLean.SkidBuffer.Challenge

/-- Three physical FIFO instances implement the complete queue-network reference. -/
theorem correctness (w : Nat) :
    RefinesAfterReset ((hardware w).denote (hardware_moore w))
      (pipelineWireSpec w) observePipeline 1 := hardware_correct w

/-- Module elaboration must introduce no additional registers. -/
theorem budget (w : Nat) : (hardware w).ffBits ≤ 3 * (2 * w + 2) :=
  Nat.le_of_eq (hardware_budget w)

end HDLean.SkidBuffer.Challenge
