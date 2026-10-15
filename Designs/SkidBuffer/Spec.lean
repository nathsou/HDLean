import HDLean.Lib.Network
import Designs.Fifo.Interface

namespace HDLean.SkidBuffer
open Fifo

/-- Three mathematical queues coupled by valid/ready, including backward pressure.
Invalid offered data is ignored; `fallback` only supplies its unobservable value. -/
def wiring (fallback : α) (i : Input α) (o : Fin 3 → Output α) : Fin 3 → Input α := fun k =>
  match k.val with
  | 0 => ⟨i.enqValid, i.enqData, (o 1).enqReady⟩
  | 1 => ⟨(o 0).deqValid, (o 0).deqData.getD fallback, (o 2).enqReady⟩
  | _ => ⟨(o 1).deqValid, (o 1).deqData.getD fallback, i.deqReady⟩

/-- Complete cycle-by-cycle reference for three two-entry queues, initially empty. -/
def pipelineSpec (fallback : α) :
    Machine (Fin 3 → List α) (Input α) (Fin 3 → Output α) :=
  Machine.network 3 (fun _ => Fifo.spec α 2) (wiring fallback)

/-- The reference accepts little-endian bit ports with the FIFO input mapping.
The fallback is unobservable whenever its corresponding valid bit is false. -/
def pipelineWireSpec (w : Nat) : Machine (Fin 3 → List (Vector Bool w))
    (Fin (w + 2) → Bool) (Fin 3 → Output (Vector Bool w)) where
  init := (pipelineSpec (Vector.replicate w false)).init
  out := (pipelineSpec (Vector.replicate w false)).out
  next q xs := (pipelineSpec (Vector.replicate w false)).next q (decodeInput xs)

end HDLean.SkidBuffer
