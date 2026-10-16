import Designs.Fifo.Spec

namespace HDLean.AsyncFifo.QueueSpec

/-- Environmental offers and independent clock edges; no physical pointer state enters the reference. -/
structure Input (α : Type) where
  writeEdge : Bool
  readEdge : Bool
  valid : Bool
  data : α
  ready : Bool

/-- Stale synchronization may suppress a transfer, but may never invent space or data. -/
def Allowed (capacity : Nat) (q : List α) (o : Fifo.Output α) : Prop :=
  (o.enqReady = true → q.length < capacity) ∧
  (o.deqValid = true → q ≠ []) ∧
  o.deqData = if o.deqValid then q.head? else none

/-- Queue contents change only on accepted domain edges, using pre-event flags. -/
def next (q : List α) (i : Input α) (o : Fifo.Output α) : List α :=
  let rest := if i.readEdge && i.ready && o.deqValid then q.tail else q
  if i.writeEdge && i.valid && o.enqReady then rest ++ [i.data] else rest

/-- A complete queue trace includes contents, conservative flags and every accepted transfer. -/
def Trace (capacity : Nat) (inputs : Nat → Input α) (outputs : Nat → Fifo.Output α)
    (queues : Nat → List α) : Prop :=
  queues 0 = [] ∧ ∀ t, Allowed capacity (queues t) (outputs t) ∧
    queues (t+1) = next (queues t) (inputs t) (outputs t)

/-- Execute the relational reference using its universally supplied conservative output oracle. -/
def run (inputs : Nat → Input α) (outputs : Nat → Fifo.Output α) : Nat → List α
  | 0 => []
  | t+1 => next (run inputs outputs t) (inputs t) (outputs t)

/-- Every interval of `gap` global steps contains an edge in this domain. -/
def EdgeFair (gap : Nat) (edge : Nat → Bool) : Prop :=
  0 < gap ∧ ∀ t, ∃ u, t ≤ u ∧ u < t+gap ∧ edge u = true

/-- A continuously offered transfer with persistent credit must complete within a finite bound. -/
def BoundedProgress (bound : Nat) (available offered transfer : Nat → Bool) : Prop :=
  ∀ t, (∀ u, t ≤ u → u < t+bound → available u = true ∧ offered u = true) →
    ∃ u, t ≤ u ∧ u < t+bound ∧ transfer u = true

end HDLean.AsyncFifo.QueueSpec
