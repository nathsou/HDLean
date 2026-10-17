import HDLean
import Designs.SkidBuffer.Spec
import Designs.Fifo.Interface

/-!
# Interface of the word-level three-stage pipeline (reviewer-owned)

The inputs are those of a FIFO (`Fifo.Word.In`): the producer's `enqValid` and
`data` enter stage 0, the consumer's `deqReady` drives stage 2. The outputs
expose every stage's `ready`, `valid` and head `data`, stage 0 first; a stage's
data is observed only when its valid bit is set. The design must be a Moore
machine; `Design.denote` views it as a machine over stores.
-/
namespace HDLean.SkidBuffer.Word
open HDLean.Rtl HDLean.Fifo

hdl_record Out (w : Nat) where
  ready0 : 1
  valid0 : 1
  data0 : w
  ready1 : 1
  valid1 : 1
  data1 : w
  ready2 : 1
  valid2 : 1
  data2 : w

/-- The ports of stage `k` as a queue output. -/
def observe (w : Nat) (outs : Array Nat) (k : Fin 3) : Output (BitVec w) :=
  let o := Bundle.decode (Out w) (outs.getD · 0)
  let port := fun (r v : BitVec 1) (d : BitVec w) =>
    (⟨r.getLsbD 0, v.getLsbD 0, if v.getLsbD 0 then some d else none⟩ : Output (BitVec w))
  match k.val with
  | 0 => port o.ready0 o.valid0 o.data0
  | 1 => port o.ready1 o.valid1 o.data1
  | _ => port o.ready2 o.valid2 o.data2

/-- The reviewed network of three two-entry queues, read through the input words. -/
def wordSpec (w : Nat) : Machine (Fin 3 → List (BitVec w)) (Array Nat) (Fin 3 → Output (BitVec w)) where
  init := (pipelineSpec (0 : BitVec w)).init
  out := (pipelineSpec (0 : BitVec w)).out
  next q ins := (pipelineSpec (0 : BitVec w)).next q (Fifo.Word.decodeInput w ins)

end HDLean.SkidBuffer.Word
