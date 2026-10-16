import Designs.Fifo.Spec
import HDLean.Core.Circuit
namespace HDLean.Fifo

/-- Two-slot skid storage. Payload is never reset. -/
structure State (α : Type) where
  valid : Bool
  full : Bool
  first : α
  second : α
  deriving Repr, BEq

/-- A local finite implementation used by the skid-buffer circuit. -/
def machine : PMachine (State α) (Input α × Bool) (Output α) where
  out s := ⟨!s.full, s.valid, if s.valid then some s.first else none⟩
  next s x :=
    let enq := x.1.enqValid && !s.full
    let deq := x.1.deqReady && s.valid
    { valid := if x.2 then false else (s.valid && !deq) || s.full || enq
      full := if x.2 then false else (s.full && !deq) || (s.valid && enq && !deq)
      first := if deq then (if s.full then s.second else x.1.enqData)
        else if !s.valid then x.1.enqData else s.first
      second := if enq then x.1.enqData else s.second }

/-- Relation to the mathematical queue; the unreachable full-without-valid state is excluded. -/
def Relation (s : State α) (q : List α) : Prop :=
  (s.full = true → s.valid = true) ∧
  q = if s.full then [s.first, s.second] else if s.valid then [s.first] else []

theorem relation_step (s : State α) (q : List α) (i : Input α) (h : Relation s q) :
    Relation (machine.next s (i, false)) ((spec α 2).next q i) := by
  obtain ⟨hv, rfl⟩ := h
  rcases s with ⟨v, f, a, b⟩
  rcases i with ⟨e, d, r⟩
  cases v <;> cases f <;> cases e <;> cases r <;>
    simp_all [Relation, machine, spec]

theorem relation_out (s : State α) (q : List α) (h : Relation s q) :
    machine.out s = (spec α 2).out q := by
  obtain ⟨hv, rfl⟩ := h
  rcases s with ⟨v, f, a, b⟩
  cases v <;> cases f <;> simp_all [machine, spec]

/-- Correctness from every power-up state, including invalid flag combinations. -/
theorem correct : RefinesAfterReset (machine (α := α)) (spec α 2) id 1 := by
  apply refinesAfterReset_of_simulation _ _ _ _ Relation
  · intro s xs hr
    have h := hr 0 (by omega)
    simp [PMachine.stateFrom, machine, h, Relation, spec]
  · exact relation_step
  · exact relation_out

/-- Two-entry circuit, for any payload width; indexed physical registers enforce finite state. -/
def hardware (w : Nat) : Circuit 0 (w + 2) (2 * w + 2) (w + 2) := Id.run do
  let valid : Expr 0 (w + 2) (2 * w + 2) := .reg ⟨0, by omega⟩
  let full : Expr 0 (w + 2) (2 * w + 2) := .reg ⟨1, by omega⟩
  let enq := Expr.and (.input ⟨0, by omega⟩) (.inv full)
  let deq := Expr.and (.input ⟨1, by omega⟩) valid
  return {
    name := s!"fifo2_w{w}"
    state := Vector.ofFn fun k =>
      if h0 : k.val = 0 then
        ⟨"valid", .synchronous false, ((Expr.and valid (.inv deq)).or full).or enq, "Designs/Fifo/Impl.lean"⟩
      else if h1 : k.val = 1 then
        ⟨"full", .synchronous false,
          (Expr.and full (.inv deq)).or (.and (.and valid enq) (.inv deq)), "Designs/Fifo/Impl.lean"⟩
      else if h : k.val < w + 2 then
        ⟨s!"head_{k.val - 2}", .unreset,
          .mux deq (.mux full (.reg ⟨k.val + w, by omega⟩) (.input ⟨k.val, h⟩))
            (.mux (.inv valid) (.input ⟨k.val, h⟩) (.reg k)), "Designs/Fifo/Impl.lean"⟩
      else
        ⟨s!"tail_{k.val - w - 2}", .unreset,
          .mux enq (.input ⟨k.val - w, by omega⟩) (.reg k), "Designs/Fifo/Impl.lean"⟩
    output := Vector.ofFn fun k =>
      if k.val = 0 then .inv full else if k.val = 1 then valid
      else .reg ⟨k.val, by omega⟩ }

end HDLean.Fifo
