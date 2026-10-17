import Designs.Toy16.Challenge
import Designs.RAM.Challenge
import HDLean.Rtl.Compact

/-!
# Challenges transfer to optimised designs

The word-level passes (`Design.optimized`: rewriting, then dead-cell removal) leave `step` and `output` unchanged, and
every challenge sees a design only through them. So each challenge holds for the
optimised design with a two-line proof: rewrite, then apply the original.
-/
namespace HDLean.Optimized
open HDLean.Rtl HDLean.Toy16 HDLean.Toy16.Word HDLean.RAM.Word

theorem toy16_retireAt (imem : Addr → Word) :
    retireAt Toy16.Word.design.optimized imem = retireAt Toy16.Word.design imem := by
  funext s₀ rst t
  simp only [retireAt, loop, fetchOut, outputsOf, Design.optimized_step, Design.optimized_output]

/-- The Toy16 challenge, for the optimised word-level core. -/
theorem toy16_correctness (imem : Addr → Word) (s₀ : Store) (rst : Nat → Bool)
    (hr : rst 0 = true) (hd : ∀ t, 0 < t → rst t = false) :
    ∃ regs mem, let retire := fun t => retireAt Toy16.Word.design.optimized imem s₀ rst (t + 1)
      RetiresLike retire (isaRetire imem (ArchState.atReset regs mem)) ∧ Progress 2 retire Retire.halt := by
  rw [toy16_retireAt]
  exact Toy16.Challenge.correctness imem s₀ rst hr hd

/-- The RAM challenge, for the optimised RAM. -/
theorem ram_correctness (a w : Nat) (ha : 0 < a) (hw : 0 < w) (s₀ : Store) (xs : Nat → Array Nat × Bool) :
    ∃ m₀ : RAMState (2 ^ a) w, ∀ t, readWord w (design a w).optimized
      ((machine (design a w).optimized).stateFrom s₀ xs t) = (ram (2 ^ a) w).runFrom m₀ (fun n => request a w (xs n).1) t := by
  simp only [readWord, machine, Design.optimized_step, Design.optimized_output]
  exact RAM.Challenge.correctness a w ha hw s₀ xs

end HDLean.Optimized
