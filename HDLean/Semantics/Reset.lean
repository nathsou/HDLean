import HDLean.Semantics.Machine

namespace HDLean

/-- Reasserting reset restarts the reference machine at that edge. Observation
remains the pre-edge output, just as it is for the physical circuit. -/
def Machine.withReset (m : Machine σ ι ο) : Machine σ (ι × Bool) ο where
  init := m.init
  out := m.out
  next s input := if input.2 then m.init else m.next s input.1

def RefinesResetSchedule (impl : PMachine σ (ι × Bool) ο) (spec : Machine τ ι π)
    (obs : ο → π) : Prop :=
  ∀ initial xs, (xs 0).2 = true → ∀ t,
    obs (impl.runFrom initial xs (1 + t)) = (spec.withReset.run (fun u => xs (1 + u)) t)

/-- One startup reset edge, then arbitrary reset assertion/release throughout
the trace. Payload garbage need not be reset or related while invalid. -/
theorem refinesResetSchedule_of_simulation
    (impl : PMachine σ (ι × Bool) ο) (spec : Machine τ ι π) (obs : ο → π)
    (R : σ → τ → Prop)
    (hreset : ∀ s i, R (impl.next s (i,true)) spec.init)
    (hstep : ∀ s q i, R s q → R (impl.next s (i,false)) (spec.next q i))
    (hout : ∀ s q, R s q → obs (impl.out s) = spec.out q) :
    RefinesResetSchedule impl spec obs := by
  intro initial xs hr t
  apply hout
  induction t with
  | zero =>
    change R (impl.next initial (xs 0)) spec.init
    rw [show xs 0 = ((xs 0).1,true) from Prod.ext rfl hr]
    exact hreset _ _
  | succ t ih =>
    simp only [Nat.add_succ, PMachine.stateFrom_succ, Machine.stateAt_succ, Machine.withReset]
    cases he : (xs (1+t)).2 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show xs (1+t) = ((xs (1+t)).1,false) from Prod.ext rfl he]
      exact hstep _ _ _ ih
    | true =>
      simp only [↓reduceIte]
      rw [show xs (1+t) = ((xs (1+t)).1,true) from Prod.ext rfl he]
      exact hreset _ _

end HDLean
