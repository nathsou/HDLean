import HDLean.Semantics.Machine
namespace HDLean.Fifo

/-- A producer offers data; a consumer independently offers readiness. -/
structure Input (α : Type) where
  enqValid : Bool
  enqData : α
  deqReady : Bool
  deriving Repr, DecidableEq, BEq

/-- Invalid data is unobservable. Readiness is determined by pre-cycle occupancy. -/
structure Output (α : Type) where
  enqReady : Bool
  deqValid : Bool
  deqData : Option α
  deriving Repr, DecidableEq, BEq

/-- Bounded reference queue. A full queue cannot enqueue, even when dequeuing this cycle. -/
def spec (α : Type) (capacity : Nat) : Machine (List α) (Input α) (Output α) where
  init := []
  out q := ⟨decide (q.length < capacity), !q.isEmpty, q.head?⟩
  next q i :=
    let q' := if i.deqReady && !q.isEmpty then q.tail else q
    if i.enqValid && decide (q.length < capacity) then q' ++ [i.enqData] else q'
end HDLean.Fifo
