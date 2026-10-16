import HDLean.Core.Syntax
import HDLean.Netlist.DagLower

namespace HDLean.Tests.Allocate
open Dag.Allocate

/-- A resettable bit and an arbitrary power-up bit, without register offsets. -/
def twoBits : Option (Dag 0 1 2 2) := circuit "two_bits" do
  let enable ← input 0
  let count ← regR
  let payload ← regN
  let toggled ← xor count.value enable
  drive count toggled
  drive payload enable
  pure #v[count.value,payload.value]

example : twoBits.isSome = true := by decide +kernel
example : (twoBits.map (·.nodes.length)) = some 4 := by decide +kernel
example : (twoBits.map (·.reset)) = some #v[.synchronous false,.unreset] := rfl

example : (run "undriven" (r := 1) (o := 0) (d := 0) (i := 0) do
    let _ ← regN
    pure #v[]).isNone = true := by decide +kernel

example : (run "duplicate" (r := 1) (o := 0) (d := 0) (i := 0) do
    let r ← regN
    drive r r.value
    drive r r.value
    pure #v[]).isNone = true := by decide +kernel

example : (run "overflow" (r := 1) (o := 0) (d := 0) (i := 0) do
    let _ ← regR
    let _ ← regN
    pure #v[]).isNone = true := by decide +kernel

example : (run "unallocated" (r := 1) (o := 0) (d := 0) (i := 0) do
    let _ ← literal false
    pure #v[]).isNone = true := by decide +kernel

/-- All Boolean initial states, input values, and reset phases. -/
example (a b x rst : Bool) :
    (twoBits.get (by decide)).lower.eval #[x,rst] #[a,b] =
      (#[(if rst then false else Bool.xor a x),x],#[a,b]) := by
  cases a <;> cases b <;> cases x <;> cases rst <;> decide +kernel

end HDLean.Tests.Allocate
