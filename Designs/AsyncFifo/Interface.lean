import Designs.AsyncFifo.Model
import Designs.AsyncFifo.Spec

/-!
Observation and startup for the dual-clock FIFO model: how its ports map to the
queue reference, how runs are formed, and what a valid reset startup is.
Reviewer-owned and frozen.
-/

namespace HDLean.AsyncFifo

/-- Ports seen by the queue reference; read data counts only when valid. -/
def observe (s : State k w) : Fifo.Output (BitVec w) :=
  ⟨enqReady s,deqValid s,if deqValid s then some (data s) else none⟩

/-- Environmental offers and clock edges, without resets or sampling masks. -/
def queueInput (i : Input k w) : QueueSpec.Input (BitVec w) :=
  ⟨i.writeEdge,i.readEdge,i.valid,i.data,i.ready⟩

/-- Physical startup and every sampling-mask choice remain explicit in the trace. -/
def stateFrom (s : State k w) (xs : Nat → Input k w) : Nat → State k w
  | 0 => s
  | t+1 => next (stateFrom s xs t) (xs t)

def seenWrite (xs : Nat → Input k w) : Nat → Bool
  | 0 => false
  | t+1 => seenWrite xs t || (xs t).writeEdge

def seenRead (xs : Nat → Input k w) : Nat → Bool
  | 0 => false
  | t+1 => seenRead xs t || (xs t).readEdge

/-- Startup requires held reset and an actual reset edge in both independent domains. -/
def Startup (xs : Nat → Input k w) (release : Nat) : Prop :=
  (∀ t, t < release → (xs t).writeReset = true ∧ (xs t).readReset = true) ∧
  seenWrite xs release = true ∧ seenRead xs release = true

end HDLean.AsyncFifo
