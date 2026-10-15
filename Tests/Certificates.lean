import HDLean
import Designs.Counter.Impl
import Designs.Fifo.Impl
namespace HDLean.Tests
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Kernel-replayed translation certificate for every state/input of a one-bit FIFO instance. -/
theorem fifo1_graph : (Backend.compile (lower (Fifo.hardware 1))).Equivalent (Fifo.hardware 1) := by
  apply Backend.Graph.validate_sound
  decide +kernel

/-- Kernel-replayed translation certificate for the complete decade counter. -/
theorem counter_graph : (Backend.compile (lower Counter.hardware)).Equivalent Counter.hardware := by
  apply Backend.Graph.validate_sound
  decide +kernel

/-- Translation validation scales with Boolean cones rather than enumerating all states. -/
theorem fifo8_graph : (Backend.compile (lower (Fifo.hardware 8))).Equivalent (Fifo.hardware 8) := by
  apply Backend.Graph.validate_sound
  decide +kernel
end HDLean.Tests
