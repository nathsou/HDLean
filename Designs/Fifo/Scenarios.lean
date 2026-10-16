import Designs.Fifo.Impl
namespace HDLean.Fifo

example : (spec Nat 2).trace [] [⟨true, 7, false⟩, ⟨true, 8, true⟩, ⟨false, 0, true⟩] =
    [⟨true, false, none⟩, ⟨true, true, some 7⟩, ⟨true, true, some 8⟩] := by decide

/-- Full/dequeue does not accept a simultaneous enqueue. -/
example : (spec Nat 2).next [7, 8] ⟨true, 9, true⟩ = [8] := by decide

/-- The known-bad never-ready implementation disagrees immediately after reset. -/
theorem rejects_never_ready : (spec Nat 2).out [] ≠ ⟨false, false, none⟩ := by decide
/-- Overwriting at full loses the oldest entry. -/
theorem rejects_overwrite : (spec Nat 2).next [7, 8] ⟨true, 9, false⟩ ≠ [8, 9] := by decide
/-- A stack returns the wrong first item. -/
theorem rejects_lifo : (spec Nat 2).out [7, 8] ≠ ⟨false, true, some 8⟩ := by decide

/-- With an always-ready consumer, the reference queue contains at most one element. -/
theorem length_le_one (cap : Nat) (xs : Nat → Input α) (hr : ∀ t, (xs t).deqReady = true) :
    ∀ t, ((spec α cap).stateAt xs t).length ≤ 1 := by
  intro t
  induction t with
  | zero => simp [Machine.stateAt, Machine.toPMachine, spec]
  | succ t ih =>
    rw [Machine.stateAt_succ]
    change (let q := (spec α cap).stateAt xs t
            let q' := if (xs t).deqReady && !q.isEmpty then q.tail else q
            if (xs t).enqValid && decide (q.length < cap) then q' ++ [(xs t).enqData] else q').length ≤ 1
    rw [hr]
    generalize hq : (spec α cap).stateAt xs t = q at *
    cases q with
    | nil => dsimp; split <;> simp_all
    | cons a tail =>
      have ht : tail = [] := by simpa using ih
      subst tail
      dsimp
      split <;> simp_all

theorem full_rate (cap : Nat) (hcap : 2 ≤ cap) (xs : Nat → Input α)
    (hr : ∀ t, (xs t).deqReady = true) (t) : ((spec α cap).run xs t).enqReady = true := by
  have h := length_le_one cap xs hr t
  change decide (((spec α cap).stateAt xs t).length < cap) = true
  simp only [decide_eq_true_eq]
  omega
end HDLean.Fifo
