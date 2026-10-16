import Designs.AsyncFifo.Progress

namespace HDLean.AsyncFifo.Challenge

/-- Complete queue behavior after real reset edges in both independent domains,
for every arbitrary power-up, clock interleaving and per-bit sampling oracle. -/
theorem correctness (s : State k w) (xs : Nat → Input k w) (release : Nat)
    (hstart : Startup xs release)
    (htraffic : ∀ t, release ≤ t → (xs t).writeReset = false ∧ (xs t).readReset = false) :
    let inputs := fun t => queueInput (xs (release+t))
    let outputs := fun t => observe (stateFrom s xs (release+t))
    QueueSpec.Trace (2^k) inputs outputs (QueueSpec.run inputs outputs) :=
  trace_refines_queue s xs release hstart htraffic

/-- Every offered write with credit completes within three fair destination-clock windows. -/
theorem enqueue_progress {s : State k w} {q : List (BitVec w)} (hqueue : QueueRelation s q)
    (xs : Nat → Input k w)
    (hr : ∀ t, (xs t).writeReset = false ∧ (xs t).readReset = false)
    (hf : QueueSpec.EdgeFair gap (fun t => (xs t).writeEdge))
    (hcredit : q.length < 2^k)
    (hoffer : ∀ t, t < 3*gap → (xs t).valid = true) :
    ∃ u, u < 3*gap ∧ push (stateFrom s xs u) (xs u) = true :=
  write_progress_queue hqueue xs hr hf hcredit hoffer

/-- Every pending queue head can be consumed within three fair read-clock windows. -/
theorem dequeue_progress {s : State k w} {q : List (BitVec w)} (hqueue : QueueRelation s q)
    (xs : Nat → Input k w)
    (hr : ∀ t, (xs t).writeReset = false ∧ (xs t).readReset = false)
    (hf : QueueSpec.EdgeFair gap (fun t => (xs t).readEdge))
    (hdata : q ≠ [])
    (hoffer : ∀ t, t < 3*gap → (xs t).ready = true) :
    ∃ u, u < 3*gap ∧ pop (stateFrom s xs u) (xs u) = true :=
  read_progress_queue hqueue xs hr hf hdata hoffer

end HDLean.AsyncFifo.Challenge
