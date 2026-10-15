import HDLean
import Designs
open HDLean HDLean.Verification

private def require (p : Bool) (message : String) : IO Unit :=
  unless p do throw (IO.userError message)

private def checkFifo (width cycles seed : Nat) : IO Unit := do
  let rows := trace (Backend.compile (lower (Fifo.hardware width))) cycles seed
  let mut q : List Nat := []
  for row in rows do
    if row.cycle > 0 then
      let actual : Fifo.Output Nat := ⟨row.outputs[0]!, row.outputs[1]!,
        if row.outputs[1]! then some (bitsToNat (row.outputs.extract 2 row.outputs.size)) else none⟩
      require (actual == (Fifo.spec Nat 2).out q) s!"FIFO mismatch width={width} cycle={row.cycle} q={q} actual={repr actual}"
    if row.inputs[width + 2]! then q := []
    else
      q := (Fifo.spec Nat 2).next q ⟨row.inputs[0]!, bitsToNat (row.inputs.extract 2 (width + 2)), row.inputs[1]!⟩

private def checkCounter (cycles seed : Nat) : IO Unit := do
  let rows := trace (Backend.compile (lower Counter.hardware)) cycles seed
  let mut count := 0
  for row in rows do
    if row.cycle > 0 then require (bitsToNat row.outputs == count) s!"counter mismatch at {row.cycle}"
    count := if row.inputs[1]! then 0 else if row.inputs[0]! then (count + 1) % 10 else count

def main : IO Unit := do
  for width in [0, 1, 2, 4, 8, 16, 32] do
    for seed in [1, 7, 42, 123, 999, 4294967295] do
      match checkCircuit (Fifo.hardware width) 200 seed with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
      checkFifo width 200 seed
  for seed in [1, 7, 42, 123, 999, 4294967295] do
    match checkCircuit Counter.hardware 200 seed with
    | .ok _ => pure ()
    | .error e => throw (IO.userError e)
    checkCounter 200 seed
  require ((Fifo.spec Nat 2).next [7,8] ⟨true,9,true⟩ == [8]) "full/dequeue convention"
  IO.println "PASS: 9,600 AST/graph cycles; 8,400 FIFO reference cycles; 1,200 counter reference cycles."
