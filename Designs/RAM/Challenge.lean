import HDLean.Lib.MemoryCircuit
namespace HDLean.RAM.Challenge
open RAMCircuit

/-- The read-data port, LSB first. -/
def readPort (out : Fin w → Bool) : BitVec w :=
  (WordExpr.inputs 0 (by omega) : WordExpr 0 w 0 w).eval out (fun k => nomatch k)

/-- For every power-up state there are initial memory contents such that the
register-array RAM's read port follows the read-before-write reference memory
on every cycle. The RAM has no reset; contents start arbitrary. -/
theorem correctness (a w : Nat) (s₀ : Fin (2^a*w+w) → Bool) (xs : Nat → (Fin (1+a+w) → Bool) × Bool) :
    ∃ m₀ : RAMState (2^a) w, ∀ t,
      readPort (((hardware a w).denote (hardware_moore a w)).runFrom s₀ xs t) =
        (ram (2^a) w).runFrom m₀ (fun n => decodeInput a w (xs n).1) t := by
  refine ⟨decode s₀, fun t => ?_⟩
  have h := decode_output a w (((hardware a w).denote (hardware_moore a w)).stateFrom s₀ xs t) (fun _ => false)
  refine h.trans ?_
  rw [hardware_correct]
  rfl

/-- Storage is `2^a` words plus the registered read word. -/
theorem budget (a w : Nat) : (hardware a w).ffBits ≤ 2^a * w + w := Nat.le_of_eq (hardware_ffBits a w)

end HDLean.RAM.Challenge
