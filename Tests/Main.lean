import HDLean
import Designs
import Tests.Backend
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

private def checkPipeline (width cycles seed : Nat) : IO Unit := do
  let rows := trace (Backend.compile (lower (SkidBuffer.hardware width))) cycles seed
  let reference := SkidBuffer.pipelineSpec (0 : Nat)
  let mut q := reference.init
  for row in rows do
    if row.cycle > 0 then
      for j in List.finRange 3 do
        let offset := j.val * (width + 2)
        let actual : Fifo.Output Nat := ⟨row.outputs[offset]!, row.outputs[offset + 1]!,
          if row.outputs[offset + 1]! then
            some (bitsToNat (row.outputs.extract (offset + 2) (offset + width + 2))) else none⟩
        require (actual == reference.out q j) s!"pipeline mismatch width={width}, cycle={row.cycle}, stage={j.val}"
    let next := if row.inputs[width + 2]! then reference.init else reference.next q
      ⟨row.inputs[0]!, bitsToNat (row.inputs.extract 2 (width + 2)), row.inputs[1]!⟩
    let snapshot := Vector.ofFn next
    q := fun j => snapshot[j]

private def checkRAM (a width cycles seed : Nat) : IO Unit := do
  let c := RAMCircuit.hardware a width
  let rows := trace (Backend.compile (lower c)) cycles seed
  let mut cells : Array Nat := Array.replicate (2^a) 0
  let mut expected := 0
  for row in rows do
    if row.cycle = 0 then
      cells := (Array.range (2^a)).map fun j => bitsToNat (row.state.extract (j*width) ((j+1)*width))
      expected := bitsToNat (row.state.extract (2^a*width) row.state.size)
    require (bitsToNat row.outputs == expected) s!"RAM mismatch depth={2^a} width={width} cycle={row.cycle}"
    let address := bitsToNat (row.inputs.extract 1 (1+a))
    expected := cells[address]!
    if row.inputs[0]! then cells := cells.set! address (bitsToNat (row.inputs.extract (1+a) (1+a+width)))

def main : IO Unit := do
  HDLean.Tests.checkBackendTexts
  for a in [0,1,2,4] do
    for w in [0,1,8,16] do
      for seed in [1,42,999] do checkRAM a w 200 seed
  IO.println "PASS: 9,600 physical RAM cycles including read/write collisions and arbitrary power-up."
  for width in [0, 1, 8, 16] do
    for seed in [1, 42, 999] do checkPipeline width 200 seed
  for width in [0, 1, 2, 4, 8, 16, 32, 64] do
    let c := Fifo.hardware width
    let g := Backend.compile (lower c)
    require (g.validate c) s!"translation validator rejected FIFO width={width}"
    let corrupt := {g with next := g.next.set! 0 (Backend.invert g.next[0]!)}
    require (!corrupt.validate c) s!"translation validator accepted corrupted FIFO width={width}"
  let counter := Backend.compile (lower Counter.hardware)
  require (counter.validate Counter.hardware) "translation validator rejected counter"
  require (!({counter with outputs := counter.outputs.set! 0 0}).validate Counter.hardware)
    "translation validator accepted a corrupted counter output"
  require (!({counter with latches := counter.latches + 1}).validate Counter.hardware)
    "translation validator accepted a malformed graph"
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
  for k in [0, 1, 2, 3, 4] do
    for seed in [1, 42, 999] do
      match Fifo.Circular.check 8 k 500 seed with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
      match AsyncFifo.check k 8 1000 seed with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
  IO.println "PASS: 7,500 circular FIFO cycles; 15,000 async oracle steps."
  IO.println "PASS: 9,600 AST/graph cycles; 8,400 FIFO reference cycles; 1,200 counter reference cycles."
  IO.println "PASS: 2,400 physical three-stage pipeline/reference cycles."
