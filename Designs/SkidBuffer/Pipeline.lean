import HDLean.Lib.Network
import Designs.Fifo.Scenarios
namespace HDLean.SkidBuffer
open Fifo

/-- Three stages coupled by valid/ready, including backward pressure. -/
def wiring (fallback : α) (i : Input α) (o : Fin 3 → Output α) : Fin 3 → Input α := fun k =>
  match k.val with
  | 0 => ⟨i.enqValid, i.enqData, (o 1).enqReady⟩
  | 1 => ⟨(o 0).deqValid, (o 0).deqData.getD fallback, (o 2).enqReady⟩
  | _ => ⟨(o 1).deqValid, (o 1).deqData.getD fallback, i.deqReady⟩

/-- The local initial state is the state after reset; payload contents remain arbitrary. -/
def stage (garbage : α) : Machine (State α) (Input α) (Output α) where
  init := ⟨false, false, garbage, garbage⟩
  out := machine.out
  next s i := machine.next s (i, false)

/-- The whole network proof is composition of the existing local FIFO proof. -/
theorem pipeline_correct (garbage : Fin 3 → α) (fallback : α) :
    Refines (Machine.network 3 (fun k => stage (garbage k)) (wiring fallback))
      (Machine.network 3 (fun _ => spec α 2) (wiring fallback)) id := by
  apply network_refines _ _ _ _ (fun _ => Relation)
  · intro k
    simp [stage, Relation, spec]
  · intro k s q i h
    exact relation_step s q i h
  · intro k s q h
    exact relation_out s q h

/-- A blocked FIFO retains its offered head word even while accepting a second word. -/
theorem output_stable (s : State α) (q : List α) (i : Input α)
    (_h : Relation s q) (hv : s.valid = true) (hr : i.deqReady = false) :
    (machine.next s (i, false)).valid = true ∧ (machine.next s (i, false)).first = s.first := by
  simp [machine, hv, hr]
end HDLean.SkidBuffer
