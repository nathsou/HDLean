import HDLean.Semantics.Machine

namespace HDLean.Verification

/-- A fixed finite instance for invariant discovery. Search is optional and
untrusted; the inductiveness and safety checks below are the proof boundary. -/
structure FiniteSystem (states inputs : Nat) where
  initial : Fin states → Bool
  next : Fin states → Fin inputs → Fin states

def FiniteSystem.check (sys : FiniteSystem n i) (candidate safe : Fin n → Bool) : Bool :=
  decide (∀ s, sys.initial s = true → candidate s = true) &&
  decide (∀ s x, candidate s = true → candidate (sys.next s x) = true) &&
  decide (∀ s, candidate s = true → safe s = true)

/-- A candidate from any oracle suffices once its finite obligations replay in
the kernel. The result covers every input stream and every permitted start. -/
theorem FiniteSystem.check_sound (sys : FiniteSystem n i) (candidate safe : Fin n → Bool)
    (checked : sys.check candidate safe = true) (s : Fin n) (hs : sys.initial s = true)
    (xs : Nat → Fin i) (t : Nat) :
    safe ((PMachine.mk id sys.next).stateFrom s xs t) = true := by
  have h := Bool.and_eq_true_iff.mp checked
  have h' := Bool.and_eq_true_iff.mp h.1
  have hi := of_decide_eq_true h'.1
  have hn := of_decide_eq_true h'.2
  have ho := of_decide_eq_true h.2
  apply ho
  induction t with
  | zero => exact hi s hs
  | succ t ih => exact hn _ _ ih

/-- Bounded reachability saturation. Running out of fuel cannot establish a
theorem: callers must check the returned candidate with `FiniteSystem.check`. -/
def FiniteSystem.search (sys : FiniteSystem n i) : Nat → List (Fin n)
  | 0 => (List.finRange n).filter (fun s => sys.initial s)
  | fuel + 1 =>
    let old := sys.search fuel
    (old ++ old.flatMap (fun s => (List.finRange i).map (sys.next s))).eraseDups

def FiniteSystem.candidate (sys : FiniteSystem n i) (fuel : Nat) : Fin n → Bool :=
  fun s => decide (s ∈ sys.search fuel)

def FiniteSystem.suggest (sys : FiniteSystem n i) (fuel : Nat) : String :=
  let reached := (sys.search fuel).map Fin.val
  s!"Reachable-state candidate: {reached}.\nTry this: use the membership predicate for this list, then prove FiniteSystem.check = true with decide +kernel. Search results alone carry no guarantee."

/-- Empty output means no sampled counterexample. This is a preflight diagnostic,
not evidence that an unsampled or infinite instance satisfies the relation. -/
def refuteSmall [Repr α] (samples : List α) (predicate : α → Bool) : String :=
  match samples.find? (fun x => !predicate x) with
  | none => ""
  | some x => s!"relation refuted at {reprStr x}"

end HDLean.Verification
