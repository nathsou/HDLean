import Designs.Counter.Proof
namespace HDLean.Counter.Challenge
/-- Exact natural-number decade behavior, from any power-up state after reset. -/
theorem correctness : RefinesAfterReset (hardware.denote moore) wireSpec value 1 := correct
/-- Four physical state bits. -/
theorem budget : (lower hardware).ffBits = 4 := ffBits
end HDLean.Counter.Challenge
