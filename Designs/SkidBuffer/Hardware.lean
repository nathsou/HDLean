import HDLean.Core.Network
import Designs.Fifo.Proof
import Designs.SkidBuffer.Pipeline
import Designs.SkidBuffer.Interface

namespace HDLean.SkidBuffer
open Fifo

/-- Physical valid/ready/data wiring between three registered FIFO instances. -/
def hardwareWiring (w : Nat) (stage : Fin 3) (port : Fin (w + 2)) :
    Circuit.Connection (w + 2) 3 (w + 2) :=
  if port.val = 1 then
    if h : stage.val = 2 then .input ⟨1, by omega⟩
    else .output ⟨stage.val + 1, by omega⟩ ⟨0, by omega⟩
  else if h : stage.val = 0 then .input port
  else .output ⟨stage.val - 1, by omega⟩
    (if port.val = 0 then ⟨1, by omega⟩ else port)

/-- Synthesizable three-stage network. Every register has one driver and every
backward ready connection reads only registered occupancy. -/
def hardware (w : Nat) : Circuit 0 (w + 2) (3 * (2 * w + 2)) (3 * (w + 2)) :=
  { Circuit.network (fun _ : Fin 3 => Fifo.hardware w) (fun _ => Fifo.hardware_moore w)
      (hardwareWiring w) with name := s!"pipeline3_w{w}" }

theorem hardware_moore (w : Nat) : (hardware w).IsMoore :=
  Circuit.network_isMoore (fun _ : Fin 3 => Fifo.hardware w)
    (fun _ => Fifo.hardware_moore w) (hardwareWiring w)

def rawWiring (s : Fin 3 → Fifo.State α) (i : Input α) : Fin 3 → Input α := fun k =>
  match k.val with
  | 0 => ⟨i.enqValid, i.enqData, !(s 1).full⟩
  | 1 => ⟨(s 0).valid, (s 0).first, !(s 2).full⟩
  | _ => ⟨(s 1).valid, (s 1).first, i.deqReady⟩

theorem decode_network_input (w : Nat) (state : Fin (3 * (2 * w + 2)) → Bool)
    (xs : Fin (w + 2) → Bool) (j : Fin 3) :
    decodeInput (Circuit.networkInputs (fun _ : Fin 3 => Fifo.hardware w)
      (hardwareWiring w) (Circuit.unpack state) xs j) =
    rawWiring (fun k => decodeState (Circuit.unpack state k)) (decodeInput xs) j := by
  rcases j with ⟨j, hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hc with rfl | rfl | rfl <;>
    simp [decodeInput, Circuit.networkInputs, hardwareWiring, Fifo.hardware,
      Circuit.evalOutput, Expr.eval, rawWiring, decodeState]
  all_goals congr 1 <;> apply Vector.ext <;> intro k hk <;>
    simp (disch := omega) [Circuit.networkInputs, hardwareWiring, Fifo.hardware,
      Circuit.evalOutput, Expr.eval, decodeState]

theorem decode_network_next (w : Nat) (state : Fin (3 * (2 * w + 2)) → Bool)
    (xs : Fin (w + 2) → Bool) (rst : Bool) (j : Fin 3) :
    decodeState (Circuit.unpack ((hardware w).next state (xs, rst)) j) =
      machine.next (decodeState (Circuit.unpack state j))
        (rawWiring (fun k => decodeState (Circuit.unpack state k)) (decodeInput xs) j, rst) := by
  have h := congrArg (fun s => decodeState (s j))
    (Circuit.network_next (fun _ : Fin 3 => Fifo.hardware w)
      (fun _ => Fifo.hardware_moore w) (hardwareWiring w) state (xs, rst))
  change decodeState (Circuit.unpack ((hardware w).next state (xs, rst)) j) = _ at h
  rw [h]
  simp only [Circuit.networkModel, Fifo.decode_next, decode_network_input]

theorem decode_network_output (w : Nat) (state : Fin (3 * (2 * w + 2)) → Bool)
    (xs : Fin (w + 2) → Bool) (j : Fin 3) :
    observePipeline ((hardware w).evalOutput state xs) j =
      machine.out (decodeState (Circuit.unpack state j)) := by
  have h := congrArg (fun os => Fifo.observe (os j))
    (Circuit.network_output (fun _ : Fin 3 => Fifo.hardware w)
      (fun _ => Fifo.hardware_moore w) (hardwareWiring w) state xs)
  change observePipeline ((hardware w).evalOutput state xs) j = _ at h
  rw [h]
  exact Fifo.decode_output _ _

theorem rawWiring_reference (fallback : α) (s : Fin 3 → Fifo.State α) (q : Fin 3 → List α)
    (h : ∀ j, Fifo.Relation (s j) (q j)) (i : Input α) (j : Fin 3) :
    (Fifo.spec α 2).next (q j) (rawWiring s i j) =
      (Fifo.spec α 2).next (q j) (wiring fallback i (fun k => (Fifo.spec α 2).out (q k)) j) := by
  have ho : (fun k => (Fifo.spec α 2).out (q k)) = fun k => machine.out (s k) := by
    funext k
    exact (Fifo.relation_out _ _ (h k)).symm
  rw [ho]
  rcases j with ⟨j, hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · rfl
  · cases hv : (s 0).valid <;> simp [rawWiring, wiring, machine, spec, hv]
  · cases hv : (s 1).valid <;> simp [rawWiring, wiring, machine, spec, hv]

/-- Exact refinement on the synthesizable pipeline AST, for every payload width,
input trace, reset schedule and arbitrary power-up state. -/
theorem hardware_correct (w : Nat) :
    RefinesAfterReset ((hardware w).denote (hardware_moore w))
      (pipelineWireSpec w) observePipeline 1 := by
  apply refinesAfterReset_of_simulation _ _ _ _
    (fun s q => ∀ j, Fifo.Relation (decodeState (Circuit.unpack s j)) (q j))
  · intro s xs hr j
    have h := hr 0 (by omega)
    change Fifo.Relation (decodeState (Circuit.unpack ((hardware w).next s (xs 0)) j)) []
    rw [show xs 0 = ((xs 0).1, (xs 0).2) from rfl, decode_network_next]
    simp [machine, h, Relation]
  · intro s q xs h j
    change Fifo.Relation (decodeState (Circuit.unpack ((hardware w).next s (xs, false)) j)) _
    rw [decode_network_next]
    have hr := Fifo.relation_step _ _
      (rawWiring (fun k => decodeState (Circuit.unpack s k)) (decodeInput xs) j) (h j)
    rw [rawWiring_reference (Vector.replicate w false) _ _ h] at hr
    exact hr
  · intro s q h
    funext j
    change observePipeline ((hardware w).evalOutput s (fun _ => false)) j = _
    rw [decode_network_output]
    exact Fifo.relation_out _ _ (h j)

/-- Flattening adds no hidden state to the three instances. -/
theorem hardware_budget (w : Nat) : (lower (hardware w)).ffBits = 3 * (2 * w + 2) := rfl

end HDLean.SkidBuffer
