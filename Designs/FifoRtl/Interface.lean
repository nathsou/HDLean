import HDLean
import Designs.Fifo.Spec

/-!
# Interface of the word-level FIFOs (reviewer-owned)

Inputs `enqValid` (one bit), `deqReady` (one bit), `data` (`w` bits); outputs
`enqReady`, `deqValid`, `data`. Output data is observed only when `deqValid` is
set. The design must be a Moore machine; `Design.denote` views it as a machine
over stores whose inputs are the port words and the reset level. Shared by the
two-entry FIFO, the general-depth FIFO and the pipeline stages.
-/
namespace HDLean.Fifo.Word
open HDLean.Rtl

hdl_record In (w : Nat) where
  enqValid : 1
  deqReady : 1
  data : w

hdl_record Out (w : Nat) where
  enqReady : 1
  deqValid : 1
  data : w

/-- The input words as a queue input. -/
def decodeInput (w : Nat) (ins : Array Nat) : Input (BitVec w) :=
  let i := Bundle.decode (In w) (ins.getD · 0)
  ⟨i.enqValid.getLsbD 0, i.data, i.deqReady.getLsbD 0⟩

/-- The output words as a queue output; data counts only when valid. -/
def observe (w : Nat) (outs : Array Nat) : Output (BitVec w) :=
  let o := Bundle.decode (Out w) (outs.getD · 0)
  ⟨o.enqReady.getLsbD 0, o.deqValid.getLsbD 0, if o.deqValid.getLsbD 0 then some o.data else none⟩

/-- The reviewed bounded queue of the given capacity, read through the input words. -/
def queueSpec (capacity w : Nat) : Machine (List (BitVec w)) (Array Nat) (Output (BitVec w)) where
  init := []
  out := (spec (BitVec w) capacity).out
  next q ins := (spec (BitVec w) capacity).next q (decodeInput w ins)

end HDLean.Fifo.Word
