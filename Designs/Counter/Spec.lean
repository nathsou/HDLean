import HDLean.Semantics.Machine
namespace HDLean.Counter
/-- Mathematical counter model for review. -/
def spec : Machine Nat Bool Nat where
  init := 0
  out := id
  next n en := if en then (n + 1) % 10 else n

end HDLean.Counter
