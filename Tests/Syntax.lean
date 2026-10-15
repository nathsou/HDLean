import HDLean.Core.Syntax

namespace HDLean.Tests

def surfaceIncrement : WordExpr 0 1 4 4 := circuit do
  let enable : Expr 0 1 4 := .input 0
  let count : WordExpr 0 1 4 4 := WordExpr.registers 0 (by decide)
  return if enable then (if count == 9 then 0 else count + 1) else count

/-- Ordinary surface syntax denotes the intended finite-width function. -/
theorem surfaceIncrement_correct (xs : Fin 1 → Bool) (state : Fin 4 → Bool) :
    surfaceIncrement.eval xs state =
      let count := (WordExpr.registers 0 (by decide) : WordExpr 0 1 4 4).eval xs state
      if xs 0 then (if count = 9 then 0 else count + 1) else count := by
  simp [surfaceIncrement, HardwareMux.select, HardwareEq.equal, WordExpr.eval_mux,
    WordExpr.equal_correct, Expr.eval]
  rw [WordExpr.eval_ofNat 9 xs state, WordExpr.eval_ofNat 0 xs state, WordExpr.eval_ofNat 1 xs state]

end HDLean.Tests
