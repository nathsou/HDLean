import Std

namespace HDLean

/-- A deterministic Moore reference model with a specified initial state. -/
structure Machine (σ ι ο : Type) where
  init : σ
  out : σ → ο
  next : σ → ι → σ

/-- Hardware has arbitrary power-up state; reset is an ordinary input. -/
structure PMachine (σ ι ο : Type) where
  out : σ → ο
  next : σ → ι → σ

def PMachine.stateFrom (m : PMachine σ ι ο) (s : σ) (xs : Nat → ι) : Nat → σ
  | 0 => s
  | t + 1 => m.next (m.stateFrom s xs t) (xs t)

def PMachine.runFrom (m : PMachine σ ι ο) (s : σ) (xs : Nat → ι) (t : Nat) : ο :=
  m.out (m.stateFrom s xs t)

def Machine.toPMachine (m : Machine σ ι ο) : PMachine σ ι ο := ⟨m.out, m.next⟩
def Machine.stateAt (m : Machine σ ι ο) (xs : Nat → ι) (t : Nat) : σ :=
  m.toPMachine.stateFrom m.init xs t
def Machine.run (m : Machine σ ι ο) (xs : Nat → ι) (t : Nat) : ο :=
  m.out (m.stateAt xs t)

def PMachine.trace (m : PMachine σ ι ο) : σ → List ι → List ο
  | _, [] => []
  | s, i :: is => m.out s :: m.trace (m.next s i) is

def Machine.trace (m : Machine σ ι ο) (s : σ) (xs : List ι) : List ο :=
  m.toPMachine.trace s xs

@[simp] theorem PMachine.stateFrom_zero (m : PMachine σ ι ο) (s : σ) (xs) :
    m.stateFrom s xs 0 = s := rfl
@[simp] theorem PMachine.stateFrom_succ (m : PMachine σ ι ο) (s : σ) (xs) (t) :
    m.stateFrom s xs (t + 1) = m.next (m.stateFrom s xs t) (xs t) := rfl
@[simp] theorem Machine.stateAt_zero (m : Machine σ ι ο) (xs) : m.stateAt xs 0 = m.init := rfl
@[simp] theorem Machine.stateAt_succ (m : Machine σ ι ο) (xs) (t) :
    m.stateAt xs (t + 1) = m.next (m.stateAt xs t) (xs t) := rfl

theorem PMachine.stateFrom_add (m : PMachine σ ι ο) (s : σ) (xs) (r t : Nat) :
    m.stateFrom s xs (r + t) = m.stateFrom (m.stateFrom s xs r) (fun u => xs (r + u)) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [Nat.add_succ, stateFrom_succ, ih]

/-- Lockstep observational refinement. -/
def Refines (impl : Machine σ ι ο) (spec : Machine τ ι π) (obs : ο → π) : Prop :=
  ∀ xs t, obs (impl.run xs t) = spec.run xs t

/-- Local simulation is sufficient for all traces, without design-specific time induction. -/
theorem Machine.refines_of_simulation (impl : Machine σ ι ο) (spec : Machine τ ι π)
    (obs : ο → π) (R : σ → τ → Prop)
    (hinit : R impl.init spec.init)
    (hstep : ∀ s q i, R s q → R (impl.next s i) (spec.next q i))
    (hout : ∀ s q, R s q → obs (impl.out s) = spec.out q) : Refines impl spec obs := by
  intro xs t
  apply hout
  induction t with
  | zero => exact hinit
  | succ t ih => exact hstep _ _ _ ih

/-- Reset for r cycles, then run: every power-up state must implement the reference. -/
def RefinesAfterReset (impl : PMachine σ (ι × Bool) ο) (spec : Machine τ ι π)
    (obs : ο → π) (r : Nat) : Prop :=
  ∀ s₀ xs, (∀ t, t < r → (xs t).2 = true) →
    (∀ t, r ≤ t → (xs t).2 = false) →
    ∀ t, obs (impl.runFrom s₀ xs (r + t)) = spec.run (fun u => (xs (r + u)).1) t

theorem refinesAfterReset_of_simulation
    (impl : PMachine σ (ι × Bool) ο) (spec : Machine τ ι π) (obs : ο → π) (r : Nat)
    (R : σ → τ → Prop)
    (hreset : ∀ s₀ xs, (∀ t, t < r → (xs t).2 = true) → R (impl.stateFrom s₀ xs r) spec.init)
    (hstep : ∀ s q i, R s q → R (impl.next s (i, false)) (spec.next q i))
    (hout : ∀ s q, R s q → obs (impl.out s) = spec.out q) :
    RefinesAfterReset impl spec obs r := by
  intro s₀ xs hr hd t
  apply hout
  induction t with
  | zero => exact hreset s₀ xs hr
  | succ t ih =>
    simp only [Nat.add_succ, PMachine.stateFrom_succ, Machine.stateAt_succ]
    have hx : xs (r + t) = ((xs (r + t)).1, false) := by
      exact Prod.ext rfl (hd _ (by omega))
    rw [hx]
    exact hstep _ _ _ ih

/-- A common reset schedule witnesses that reset assumptions are satisfiable. -/
def resetSchedule (r : Nat) (xs : Nat → ι) (t : Nat) : ι × Bool := (xs t, decide (t < r))
theorem resetSchedule_valid (r : Nat) (xs : Nat → ι) :
    (∀ t, t < r → (resetSchedule r xs t).2 = true) ∧
    (∀ t, r ≤ t → (resetSchedule r xs t).2 = false) := by
  simp [resetSchedule]

/-- Reset refinement implies independence of arbitrary initial hardware contents. -/
theorem reset_noninterference {impl : PMachine σ (ι × Bool) ο}
    {spec : Machine τ ι π} {obs : ο → π} {r : Nat}
    (h : RefinesAfterReset impl spec obs r)
    (a b : σ) (xs) (hr : ∀ t, t < r → (xs t).2 = true)
    (hd : ∀ t, r ≤ t → (xs t).2 = false) (t) :
    obs (impl.runFrom a xs (r + t)) = obs (impl.runFrom b xs (r + t)) := by
  rw [h a xs hr hd, h b xs hr hd]

end HDLean
