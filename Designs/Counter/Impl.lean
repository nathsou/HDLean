import HDLean.Netlist.Lower
import HDLean.Core.Syntax
import Designs.Counter.Spec
namespace HDLean.Counter

/-- Four-bit decade counter with enable and synchronous reset. Invalid power-up values are allowed. -/
def hardware : Circuit 0 1 4 4 := circuit do
  let count : WordExpr 0 1 4 4 := WordExpr.registers 0 (by decide)
  let en : Expr 0 1 4 := .input 0
  let atNine := WordExpr.eq count (WordExpr.literal 9)
  let increment := WordExpr.add count (WordExpr.literal 1)
  let next := WordExpr.mux en (WordExpr.mux atNine (WordExpr.literal 0) increment) count
  return { name := "decade"
           state := Vector.ofFn fun k => ⟨s!"count_{k.val}", .synchronous false, next[k], "Designs/Counter/Impl.lean"⟩
           output := count }

/-- Exact structural budget, independent of any synthesis tool. -/
theorem ffBits : (lower hardware).ffBits = 4 := rfl
end HDLean.Counter
