import HDLean.Tactics.Diagnostics

namespace HDLean.Tests
open Verification

def smallCounter : FiniteSystem 4 2 where
  initial s := s.val == 0
  next s _ := if h : s.val < 2 then ⟨s.val + 1, by omega⟩ else 0

/-- The search oracle produces a candidate whose full finite obligations replay. -/
theorem discovered_counter : smallCounter.check (smallCounter.candidate 4)
    (fun s => s.val < 3) = true := by decide +kernel

/-- An overbroad invariant is rejected by its safety obligation. -/
example : smallCounter.check (fun _ => true) (fun s => s.val < 3) = false := by decide +kernel

example : True := by
  refute_small [0,1,2] with (fun n : Nat => n < 3)
  fail_if_success refute_small [0,1,3] with (fun n : Nat => n < 3)
  trivial

end HDLean.Tests
