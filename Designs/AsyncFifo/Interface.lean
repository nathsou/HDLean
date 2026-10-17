import HDLean
import Designs.AsyncFifo.Spec

/-!
# Interface of the dual-clock FIFO (reviewer-owned)

The environment of each global step (`Input`): independent write and read clock
edges, a reset level per domain, the producer's offer, the consumer's
readiness, and the sampling masks of the two pointer synchronizers. `Startup`
is what a valid reset startup is.

The word-level design is a multi-clock design (`MDesign`) with two domains:
domain 0 writes, domain 1 reads. `Word.event` turns an environment step into a
multi-clock event: the write domain's external inputs are `valid` and `data`,
the read domain's is `ready`; crossing 0 is sampled by the read domain with the
read mask, crossing 1 by the write domain with the write mask. `Word.observe`
reads the ports the queue reference sees: write-domain output 0 (`ready`) and
read-domain outputs 0 and 1 (`valid` and `data`), with idle inputs; read data
counts only when valid.
-/

namespace HDLean.AsyncFifo

/-- Edges, resets, and metastability masks are explicit independent environmental inputs. -/
structure Input (k w : Nat) where
  writeEdge : Bool
  readEdge : Bool
  writeReset : Bool
  readReset : Bool
  valid : Bool
  data : BitVec w
  ready : Bool
  writeMask : BitVec (k + 1)
  readMask : BitVec (k + 1)

/-- Environmental offers and clock edges, without resets or sampling masks. -/
def queueInput (i : Input k w) : QueueSpec.Input (BitVec w) :=
  ⟨i.writeEdge,i.readEdge,i.valid,i.data,i.ready⟩

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

namespace Word
open HDLean.Rtl

/-- One environment step as a multi-clock event. -/
def event (i : Input k w) : MDesign.Event :=
  ⟨#[#[i.valid.toNat, i.data.toNat], #[i.ready.toNat]], #[i.writeReset, i.readReset],
    #[i.writeEdge, i.readEdge], #[i.readMask.toNat, i.writeMask.toNat]⟩

/-- No edge, no reset, no offer: the inputs under which ports are read. -/
def idle : MDesign.Event := ⟨#[#[0, 0], #[0]], #[false, false], #[false, false], #[0, 0]⟩

/-- Ports seen by the queue reference; read data counts only when valid. -/
def observe (w : Nat) (md : MDesign) (s : MDesign.State) : Fifo.Output (BitVec w) :=
  let ready := ((md.outputs s idle 0).getD 0 0).testBit 0
  let valid := ((md.outputs s idle 1).getD 0 0).testBit 0
  ⟨ready, valid, if valid then some (bv w ((md.outputs s idle 1).getD 1 0)) else none⟩

/-- The multi-clock state after each environment step. -/
def stateFrom (md : MDesign) (s : MDesign.State) (xs : Nat → Input k w) : Nat → MDesign.State :=
  md.stateFrom s (fun t => event (xs t))

/-- A write is transferred: a write edge out of reset, offered data, and space observed. -/
def push (w : Nat) (md : MDesign) (s : MDesign.State) (i : Input k w) : Bool :=
  i.writeEdge && !i.writeReset && i.valid && (observe w md s).enqReady

/-- A read is transferred: a read edge out of reset, a ready consumer, and data observed. -/
def pop (w : Nat) (md : MDesign) (s : MDesign.State) (i : Input k w) : Bool :=
  i.readEdge && !i.readReset && i.ready && (observe w md s).deqValid

end Word

end HDLean.AsyncFifo
