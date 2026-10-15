import Designs.Counter.Impl
import Designs.Counter.Interface
namespace HDLean.Counter

def unpack (a b c d : Bool) : Fin 4 → Bool := fun k =>
  match k.val with | 0 => a | 1 => b | 2 => c | _ => d

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem step_table : ∀ a b c d en rst : Bool,
    (value (unpack a b c d) < 10 ∨ rst = true) →
    value (hardware.next (unpack a b c d) ((fun _ => en), rst)) =
      if rst then 0 else if en then (value (unpack a b c d) + 1) % 10 else value (unpack a b c d) := by
  decide +kernel

private theorem unpack_state (s : Fin 4 → Bool) : unpack (s 0) (s 1) (s 2) (s 3) = s := by
  funext k
  rcases k with ⟨k,h⟩
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n + 4 => omega

private theorem input_single (xs : Fin 1 → Bool) : (fun _ => xs 0) = xs := by
  funext k
  have : k = 0 := by apply Fin.ext; omega
  subst k
  rfl

theorem next_correct (s : Fin 4 → Bool) (xs : Fin 1 → Bool) (rst : Bool)
    (h : value s < 10 ∨ rst = true) :
    value (hardware.next s (xs, rst)) = if rst then 0 else if xs 0 then (value s + 1) % 10 else value s := by
  have ht := step_table (s 0) (s 1) (s 2) (s 3) (xs 0) rst
  simpa only [unpack_state, input_single] using ht h

theorem moore : hardware.IsMoore := by
  intro s a b
  funext k
  simp [Circuit.evalOutput, hardware, WordExpr.registers, Expr.eval]

private theorem output_value (s : Fin 4 → Bool) : value (hardware.denote moore |>.out s) = value s := rfl

/-- The emitted counter implements the natural-number decade spec from arbitrary power-up state. -/
theorem correct : RefinesAfterReset (hardware.denote moore) wireSpec value 1 := by
  apply refinesAfterReset_of_simulation _ _ _ _ (fun s q => value s = q ∧ q < 10)
  · intro s xs hr
    have h := hr 0 (by omega)
    change value (hardware.next s (xs 0)) = 0 ∧ 0 < 10
    rw [show xs 0 = ((xs 0).1, (xs 0).2) from rfl, next_correct _ _ _ (Or.inr h), h]
    simp
  · intro s q xs h
    change value (hardware.next s (xs, false)) = _ ∧ _
    rw [next_correct s xs false (Or.inl (by omega))]
    simp only [Bool.false_eq_true, ↓reduceIte, wireSpec, spec, h.1]
    constructor
    · trivial
    · split
      · exact Nat.mod_lt _ (by decide)
      · exact h.2
  · intro s q h
    exact h.1
end HDLean.Counter
