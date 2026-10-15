import HDLean.Semantics.Composition
namespace HDLean
structure StreamPorts (α : Type) where
  valid : Bool
  ready : Bool
  data : α

/-- Offered data remains stable under backpressure. -/
def Stable (p : Nat → StreamPorts α) : Prop :=
  ∀ t, (p t).valid = true → (p t).ready = false →
    (p (t + 1)).valid = true ∧ (p (t + 1)).data = (p t).data

/-- A guarded method fires exactly when producer and consumer agree. -/
structure Method (α : Type) where
  offer : Option α
  ready : Bool

def Method.fire (m : Method α) : Option α := if m.ready then m.offer else none

theorem Method.no_fire_when_blocked (m : Method α) (h : m.ready = false) : m.fire = none := by
  simp [Method.fire, h]

/-- Mapping a stream preserves its protocol independently of payload representation. -/
theorem Stable.map (p : Nat → StreamPorts α) (f : α → β) (h : Stable p) :
    Stable (fun t => ⟨(p t).valid, (p t).ready, f (p t).data⟩) := by
  intro t hv hr
  obtain ⟨a, b⟩ := h t hv hr
  exact ⟨a, congrArg f b⟩

/-- Round-robin arbiter with an explicit grant. State is the next preferred requester. -/
def arbitrate2 (preferRight left right : Bool) : Option Bool :=
  if left && right then some preferRight else if left then some false else if right then some true else none

theorem arbitrate2_sound (p l r : Bool) :
    (arbitrate2 p l r = some false → l = true) ∧
    (arbitrate2 p l r = some true → r = true) := by
  cases p <;> cases l <;> cases r <;> decide
end HDLean
