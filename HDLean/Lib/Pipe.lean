import HDLean.Semantics.Machine
namespace HDLean

/-- A causal stream transducer with a proved, fixed latency. -/
structure Pipe (n : Nat) (α β : Type) where
  run : (Nat → α) → Nat → β
  function : α → β
  causal : ∀ xs ys t, (∀ u, u ≤ t → xs u = ys u) → run xs t = run ys t
  correct : ∀ xs t, run xs (t + n) = function (xs t)

namespace Pipe
/-- A combinational pipe has zero latency; unlike a Moore-only model, this is inhabited. -/
def comb (f : α → β) : Pipe 0 α β where
  run xs t := f (xs t)
  function := f
  causal _xs _ys t h := congrArg f (h t (Nat.le_refl _))
  correct _ _ := rfl

/-- Sequential composition adds latencies. -/
def seq (a : Pipe n α β) (b : Pipe m β γ) : Pipe (n + m) α γ where
  run xs := b.run (a.run xs)
  function := b.function ∘ a.function
  causal xs ys t h := b.causal _ _ t fun u hu =>
    a.causal xs ys u fun v hv => h v (Nat.le_trans hv hu)
  correct xs t := by
    rw [← Nat.add_assoc, b.correct, a.correct]
    rfl

/-- Parallel paths must have the same latency; unequal joins do not typecheck. -/
def par (a : Pipe n α β) (b : Pipe n α γ) : Pipe n α (β × γ) where
  run xs t := (a.run xs t, b.run xs t)
  function x := (a.function x, b.function x)
  causal xs ys t h := Prod.ext (a.causal _ _ _ h) (b.causal _ _ _ h)
  correct xs t := by rw [a.correct, b.correct]

/-- Explicit startup contents model uninitialized delay storage. -/
def delay (k : Nat) (startup : Nat → β) (a : Pipe n α β) : Pipe (n + k) α β where
  run xs t := if t < k then startup t else a.run xs (t - k)
  function := a.function
  causal xs ys t h := by
    split
    · rfl
    · apply a.causal
      intro u hu
      apply h
      omega
  correct xs t := by
    have ht : ¬t + (n + k) < k := by omega
    simp only [ht, ↓reduceIte]
    rw [show t + (n + k) - k = t + n by omega]
    exact a.correct xs t
end Pipe
end HDLean
