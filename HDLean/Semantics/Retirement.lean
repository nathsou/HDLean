import HDLean.Semantics.Machine
namespace HDLean

def retiredBefore (retire : Nat → Option α) : Nat → Nat
  | 0 => 0
  | t + 1 => retiredBefore retire t + if (retire t).isSome then 1 else 0

/-- Bubbles are allowed, but every retirement must be the next reference event. -/
def RetiresLike (retire : Nat → Option α) (reference : Nat → α) : Prop :=
  ∀ t a, retire t = some a → a = reference (retiredBefore retire t)

/-- An abstract instruction machine advances only on an architectural event. -/
def iterate (step : σ → σ) (initial : σ) : Nat → σ
  | 0 => initial
  | n + 1 => step (iterate step initial n)

/-- Local stuttering simulation with a flush/abstraction relation supplied by the implementation. -/
theorem retiresLike_of_simulation
    (impl : Machine σ ι (Option α)) (step : τ → τ) (initial : τ) (event : τ → α)
    (R : σ → τ → Prop) (hinit : R impl.init initial)
    (hbubble : ∀ s q i, R s q → impl.out s = none → R (impl.next s i) q)
    (hretire : ∀ s q i a, R s q → impl.out s = some a →
      a = event q ∧ R (impl.next s i) (step q)) (xs : Nat → ι) :
    RetiresLike (impl.run xs) (fun n => event (iterate step initial n)) := by
  have rel : ∀ t, R (impl.stateAt xs t)
      (iterate step initial (retiredBefore (impl.run xs) t)) := by
    intro t
    induction t with
    | zero => exact hinit
    | succ t ih =>
      rw [Machine.stateAt_succ, retiredBefore]
      cases h : impl.run xs t with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact hbubble _ _ _ ih h
      | some a =>
        simp only [Option.isSome_some, ↓reduceIte, iterate]
        exact (hretire _ _ _ _ ih h).2
  intro t a h
  exact (hretire _ _ (xs t) _ (rel t) h).1

/-- Progress explicitly accounts for termination, so a permanently stalled live core fails. -/
def Progress (K : Nat) (retire : Nat → Option α) (isHalt : α → Bool) : Prop :=
  ∀ t, (∃ u, t ≤ u ∧ u < t + K ∧ (retire u).isSome = true) ∨
    (∃ u a, u < t ∧ retire u = some a ∧ isHalt a = true)
end HDLean
