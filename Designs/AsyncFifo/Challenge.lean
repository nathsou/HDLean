import Designs.AsyncFifo.Word

/-!
Dual-clock FIFO on word-level RTL: a multi-clock design with a write domain and
a read domain that see each other's Gray pointers only through two-flop
synchronizers, and share one memory.
-/

namespace HDLean.AsyncFifo.Challenge
open HDLean.Rtl HDLean.AsyncFifo.Word

/-- After a reset startup in both domains, the observed ports follow the queue
reference for every power-up state (memory included), clock interleaving and
sampling oracle, for every positive depth exponent and payload width.
Implementation hole: `AsyncFifo.Word.design`. -/
theorem correctness (k w : Nat) (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (xs : Nat → Input k w) (release : Nat)
    (hstart : Startup xs release)
    (htraffic : ∀ t, release ≤ t → (xs t).writeReset = false ∧ (xs t).readReset = false) :
    let inputs := fun t => queueInput (xs (release + t))
    let outputs := fun t => Word.observe w (AsyncFifo.Word.design k w) (Word.stateFrom (AsyncFifo.Word.design k w) S xs (release + t))
    QueueSpec.Trace (2 ^ k) inputs outputs (QueueSpec.run inputs outputs) :=
  AsyncFifo.Word.correct k w hk hw S xs release hstart htraffic

/-- A write offered while the reference queue has space completes within three
fair write-clock windows. Without this, a FIFO that never accepts would pass. -/
theorem enqueue_progress (k w : Nat) (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (xs : Nat → Input k w)
    (release t gap : Nat) (hstart : Startup xs release)
    (htraffic : ∀ u, release ≤ u → (xs u).writeReset = false ∧ (xs u).readReset = false)
    (hf : QueueSpec.EdgeFair gap (fun u => (xs (release + t + u)).writeEdge))
    (hcredit : (QueueSpec.run (fun u => queueInput (xs (release + u)))
        (fun u => Word.observe w (AsyncFifo.Word.design k w) (Word.stateFrom (AsyncFifo.Word.design k w) S xs (release + u))) t).length < 2 ^ k)
    (hoffer : ∀ u, u < 3 * gap → (xs (release + t + u)).valid = true) :
    ∃ u, u < 3 * gap ∧ Word.push w (AsyncFifo.Word.design k w)
      (Word.stateFrom (AsyncFifo.Word.design k w) S xs (release + t + u)) (xs (release + t + u)) = true :=
  AsyncFifo.Word.enqueue_progress k w hk hw S xs release t gap hstart htraffic hf hcredit hoffer

/-- A nonempty reference queue is read within three fair read-clock windows. -/
theorem dequeue_progress (k w : Nat) (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (xs : Nat → Input k w)
    (release t gap : Nat) (hstart : Startup xs release)
    (htraffic : ∀ u, release ≤ u → (xs u).writeReset = false ∧ (xs u).readReset = false)
    (hf : QueueSpec.EdgeFair gap (fun u => (xs (release + t + u)).readEdge))
    (hdata : QueueSpec.run (fun u => queueInput (xs (release + u)))
        (fun u => Word.observe w (AsyncFifo.Word.design k w) (Word.stateFrom (AsyncFifo.Word.design k w) S xs (release + u))) t ≠ [])
    (hoffer : ∀ u, u < 3 * gap → (xs (release + t + u)).ready = true) :
    ∃ u, u < 3 * gap ∧ Word.pop w (AsyncFifo.Word.design k w)
      (Word.stateFrom (AsyncFifo.Word.design k w) S xs (release + t + u)) (xs (release + t + u)) = true :=
  AsyncFifo.Word.dequeue_progress k w hk hw S xs release t gap hstart htraffic hf hdata hoffer

end HDLean.AsyncFifo.Challenge
