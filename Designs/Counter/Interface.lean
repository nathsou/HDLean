import Designs.Counter.Spec
namespace HDLean.Counter
def value (s : Fin 4 → Bool) : Nat :=
  (if s 0 then 1 else 0) + (if s 1 then 2 else 0) + (if s 2 then 4 else 0) + (if s 3 then 8 else 0)

def wireSpec : Machine Nat (Fin 1 → Bool) Nat where
  init := 0
  out := id
  next n xs := spec.next n (xs 0)

end HDLean.Counter
