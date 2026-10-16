import Designs.Fifo.CircularHardware

namespace HDLean.Fifo.Circular.Physical

/-- Only finite bit inputs are decoded; the reference state remains a mathematical list. -/
def queueSpec (k w : Nat) : Machine (List (BitVec w)) (Fin (w+2) → Bool) (Output (BitVec w)) where
  init := []
  out := (Fifo.spec (BitVec w) (2^k)).out
  next q i := (Fifo.spec (BitVec w) (2^k)).next q (decodeInput k w i)

end HDLean.Fifo.Circular.Physical
