import HDLean.Semantics.Machine
namespace HDLean

/-- Parallel Moore machines read the same input; no instantaneous feedback is introduced. -/
def Machine.parallel (a : Machine σ ι ο) (b : Machine τ ι π) : Machine (σ × τ) ι (ο × π) where
  init := (a.init, b.init)
  out s := (a.out s.1, b.out s.2)
  next s i := (a.next s.1 i, b.next s.2 i)

/-- Sequential Moore composition observes the upstream pre-edge output. -/
def Machine.seq (a : Machine σ ι ο) (b : Machine τ ο π) : Machine (σ × τ) ι π where
  init := (a.init, b.init)
  out s := b.out s.2
  next s i := (a.next s.1 i, b.next s.2 (a.out s.1))

theorem Machine.parallel_state (a : Machine σ ι ο) (b : Machine τ ι π) (xs) (t) :
    (a.parallel b).stateAt xs t = (a.stateAt xs t, b.stateAt xs t) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [Machine.stateAt_succ, ih]; rfl

theorem Refines.parallel {a : Machine σ ι ο} {a' : Machine σ' ι ο'}
    {b : Machine τ ι π} {b' : Machine τ' ι π'} {f : ο → ο'} {g : π → π'}
    (ha : Refines a a' f) (hb : Refines b b' g) :
    Refines (a.parallel b) (a'.parallel b') (fun x => (f x.1, g x.2)) := by
  intro xs t
  unfold Machine.run
  rw [Machine.parallel_state, Machine.parallel_state]
  exact Prod.ext (ha xs t) (hb xs t)

/-- Finite-history assume/guarantee contracts make circular composition sound. -/
structure CausalContract (A B : Nat → Prop) : Prop where
  initial : B 0
  step : ∀ t, (∀ u, u ≤ t → A u) → (∀ u, u ≤ t → B u) → B (t + 1)

/-- Each component may depend only on the other component's history, never its current guarantee. -/
theorem compose_contracts (ab : CausalContract A B) (ba : CausalContract B A) :
    ∀ t, A t ∧ B t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    cases t with
    | zero => exact ⟨ba.initial, ab.initial⟩
    | succ t =>
      have ha : ∀ u, u ≤ t → A u := fun u hu => (ih u (by omega)).1
      have hb : ∀ u, u ≤ t → B u := fun u hu => (ih u (by omega)).2
      exact ⟨ba.step t hb ha, ab.step t ha hb⟩

/-- A bounded-history invariant packages k-induction's base window and one local closure rule. -/
theorem k_induction (P : Nat → Prop) (k : Nat) (_hk : 0 < k)
    (base : ∀ t, t < k → P t)
    (step : ∀ t, (∀ j, j < k → P (t + j)) → P (t + k)) : ∀ t, P t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases h : t < k
    · exact base t h
    · have he : t - k + k = t := by omega
      rw [← he]
      apply step
      intro j hj
      apply ih
      omega
end HDLean
