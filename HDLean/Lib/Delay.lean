import HDLean.Core.WordBank
import HDLean.Lib.MemoryCircuit
import HDLean.Lib.Pipe

set_option backward.isDefEq.respectTransparency false

namespace HDLean.Delay

/-- A finite word delay. Every stage is real, unreset storage; zero stages
is the input wire and consumes no state. -/
def hardware (stages width : Nat) : Circuit 0 width (stages * width) width :=
  wordBank s!"delay_{stages}x{width}" (fun _ => .unreset)
    (fun j => if _h : j.val = 0 then WordExpr.inputs 0 (by omega)
      else bankWord ⟨j.val - 1, by omega⟩)
    (if h : stages = 0 then WordExpr.inputs 0 (by omega)
      else bankWord ⟨stages - 1, by omega⟩)

def inputBits (value : BitVec width) : Fin width → Bool := fun k => value.getLsbD k.val

def stateAt (stages width : Nat) (initial : Fin (stages * width) → Bool)
    (xs : Nat → BitVec width) : Nat → Fin (stages * width) → Bool
  | 0 => initial
  | t + 1 => (hardware stages width).next (stateAt stages width initial xs t)
      (inputBits (xs t), false)

def observe (stages width : Nat) (initial : Fin (stages * width) → Bool)
    (xs : Nat → BitVec width) (t : Nat) : BitVec width :=
  WordExpr.eval (hardware stages width).output (inputBits (xs t))
    (stateAt stages width initial xs t)

@[simp] theorem input_word (value : BitVec width) (state : Fin r → Bool) :
    (WordExpr.inputs 0 (by omega) : WordExpr d width r width).eval (inputBits value) state = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [WordExpr.eval_bit _ _ _ k hk]
  simp [WordExpr.inputs, Expr.eval, inputBits]

theorem stage_next (j : Fin stages) (s : Fin (stages * width) → Bool) (x y : BitVec width) :
    (bankWord j : WordExpr 0 width (stages * width) width).eval (inputBits y)
      ((hardware stages width).next s (inputBits x, false)) =
      if _h : j.val = 0 then x else
        (bankWord ⟨j.val - 1, by omega⟩ : WordExpr 0 width (stages * width) width).eval
          (inputBits x) s := by
  rw [bankWord_inputs _ _ (inputBits y) (inputBits x)]
  unfold hardware
  rw [wordBank_next]
  by_cases h : j.val = 0
  · simp only [h, ↓reduceDIte, input_word]
  · simp only [h, ↓reduceDIte]

/-- Warmup is exactly the number of physical registers on the path, regardless
of their initial contents. -/
theorem stage_after (j : Nat) (hj : j < stages) (initial : Fin (stages * width) → Bool)
    (xs : Nat → BitVec width) (t : Nat) :
    (bankWord ⟨j,hj⟩ : WordExpr 0 width (stages * width) width).eval
      (inputBits (xs (t + (j + 1)))) (stateAt stages width initial xs (t + (j + 1))) = xs t := by
  induction j with
  | zero =>
    rw [show t + (0 + 1) = t + 1 by omega, stateAt, stage_next]
    simp
  | succ j ih =>
    rw [show t + (j + 1 + 1) = (t + (j + 1)) + 1 by omega, stateAt, stage_next]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_sub_cancel]
    exact ih (by omega)

theorem latency (stages width : Nat) (initial : Fin (stages * width) → Bool)
    (xs : Nat → BitVec width) (t : Nat) :
    observe stages width initial xs (t + stages) = xs t := by
  by_cases h : stages = 0
  · subst stages
    simp [observe, hardware, wordBank, input_word]
  · have hs : stages - 1 < stages := by omega
    have hp := stage_after (stages - 1) hs initial xs t
    simpa only [observe, hardware, wordBank, h, ↓reduceDIte,
      show stages - 1 + 1 = stages by omega] using hp

/-- Moving a pure combinational function across a register bank preserves all
observations after warmup, even when the two banks power up independently. -/
theorem retime (f : BitVec width → BitVec outWidth) (stages : Nat)
    (left : Fin (stages * width) → Bool) (right : Fin (stages * outWidth) → Bool)
    (xs : Nat → BitVec width) (t : Nat) :
    f (observe stages width left xs (t + stages)) =
      observe stages outWidth right (fun u => f (xs u)) (t + stages) := by
  rw [latency, latency]

/-- The existing stream contract and the finite circuit agree after startup. -/
theorem realizes_pipe (stages width : Nat) (initial : Fin (stages * width) → Bool)
    (startup : Nat → BitVec width) (xs : Nat → BitVec width) (t : Nat) :
    observe stages width initial xs (t + stages) =
      (Pipe.delay stages startup (Pipe.comb id)).run xs (t + stages) := by
  rw [latency]
  simpa [Pipe.delay, Pipe.comb] using
    ((Pipe.delay stages startup (Pipe.comb id)).correct xs t).symm

theorem storage_bits (stages width : Nat) :
    (hardware stages width).state.size = stages * width := by simp

end HDLean.Delay
