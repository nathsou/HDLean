import Designs.AsyncFifo.Progress

/-!
Dual-clock FIFO, model level. The model (`Model.lean`) has independent clock
edges and per-bit sampling masks; its hardware link still uses the legacy
multi-clock circuits and is not part of this challenge (milestone R2).
-/

namespace HDLean.AsyncFifo.Challenge

/-- After a reset startup in both domains, the observed ports follow the queue
reference for every power-up state, clock interleaving and sampling oracle. -/
theorem correctness (s : State k w) (xs : Nat → Input k w) (release : Nat)
    (hstart : Startup xs release)
    (htraffic : ∀ t, release ≤ t → (xs t).writeReset = false ∧ (xs t).readReset = false) :
    let inputs := fun t => queueInput (xs (release+t))
    let outputs := fun t => observe (stateFrom s xs (release+t))
    QueueSpec.Trace (2^k) inputs outputs (QueueSpec.run inputs outputs) :=
  trace_refines_queue s xs release hstart htraffic

/-- A write offered while the reference queue has space completes within three
fair write-clock windows. Without this, a FIFO that never accepts would pass. -/
theorem enqueue_progress (s : State k w) (xs : Nat → Input k w) (release t gap : Nat)
    (hstart : Startup xs release)
    (htraffic : ∀ u, release ≤ u → (xs u).writeReset = false ∧ (xs u).readReset = false)
    (hf : QueueSpec.EdgeFair gap (fun u => (xs (release+t+u)).writeEdge))
    (hcredit : (QueueSpec.run (fun u => queueInput (xs (release+u)))
        (fun u => observe (stateFrom s xs (release+u))) t).length < 2^k)
    (hoffer : ∀ u, u < 3*gap → (xs (release+t+u)).valid = true) :
    ∃ u, u < 3*gap ∧ push (stateFrom s xs (release+t+u)) (xs (release+t+u)) = true :=
  write_progress_after_startup s xs release t gap hstart htraffic hf hcredit hoffer

/-- A nonempty reference queue is read within three fair read-clock windows. -/
theorem dequeue_progress (s : State k w) (xs : Nat → Input k w) (release t gap : Nat)
    (hstart : Startup xs release)
    (htraffic : ∀ u, release ≤ u → (xs u).writeReset = false ∧ (xs u).readReset = false)
    (hf : QueueSpec.EdgeFair gap (fun u => (xs (release+t+u)).readEdge))
    (hdata : QueueSpec.run (fun u => queueInput (xs (release+u)))
        (fun u => observe (stateFrom s xs (release+u))) t ≠ [])
    (hoffer : ∀ u, u < 3*gap → (xs (release+t+u)).ready = true) :
    ∃ u, u < 3*gap ∧ pop (stateFrom s xs (release+t+u)) (xs (release+t+u)) = true :=
  read_progress_after_startup s xs release t gap hstart htraffic hf hdata hoffer

end HDLean.AsyncFifo.Challenge
