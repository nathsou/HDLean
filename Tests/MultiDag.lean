import HDLean.MultiClock.Dag

namespace HDLean.MultiClock.Shared.Tests

def crossing : MultiDag 2 where
  inputs := fun _ => 1
  regs := fun _ => 1
  outputs := fun _ => 1
  syncCount := fun _ => 1
  sync := fun _ _ => ⟨⟨0,by decide⟩,1,#v[⟨0,by decide⟩]⟩
  localInputs := fun _ => 1
  port := fun d _ => if d.val = 0 then .input ⟨0,by decide⟩ else .synchronized ⟨0,by decide⟩ ⟨0,by decide⟩
  logic := fun _ => {
    name := "domain"
    nodes := [.input ⟨0,by decide⟩,.reg ⟨0,by decide⟩]
    next := #v[0]
    out := #v[1]
    reset := #v[.synchronous false]
    wf := by simp [Dag.WellFormed,Dag.NodesWF,Dag.Op.Valid] }

def initial : crossing.State := ⟨fun _ _ => false,fun _ _ _ => false,fun _ _ _ => false⟩
def event (new : Bool) : crossing.Event :=
  ⟨fun _ _ => true,fun _ => false,fun _ => true,fun _ _ _ => new⟩

-- Coincident source/destination edges expose BOTH physically possible first-stage outcomes.
example : (crossing.next initial (event false)).first ⟨1,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ = false := rfl
example : (crossing.next initial (event true)).first ⟨1,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ = true := rfl
example (new : Bool) : (crossing.next initial (event new)).second ⟨1,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ = false := rfl
example : (crossing.lower.eval initial (event true)).1.first ⟨1,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ = true := by
  rw [MultiDag.lower_correct]
  rfl
example (trace : Nat → crossing.State) (edges : Nat → Fin 2 → Bool) : crossing.SourceSafe trace edges :=
  crossing.sourceSafe_single_bit (by intro d k; rfl) trace edges

#print axioms HDLean.MultiClock.Shared.MultiDag.lower_correct
end HDLean.MultiClock.Shared.Tests
