import HDLean
import Designs
import Lean
open HDLean HDLean.Backend HDLean.Verification

private def usage : String := "HDLean 0.2.0\n\
  hdlean emit <fifo|counter|pipeline|ram|ring|toy16> <sv|aiger|rtlil> <path> [width=8]\n\
  hdlean emit-async <sv|rtlil|aiger> <path> [width=8] [log2depth=4]   (clock edges as inputs)\n\
  hdlean metrics <fifo|counter|pipeline|ram|ring|toy16> [width=8]\n\
  hdlean trace <fifo|counter|pipeline|ram|ring|toy16> <path.json> [width=8] [cycles=60] [seed=1]\n\
  hdlean check <fifo|counter|pipeline|ram|ring|toy16> [width=8] [cycles=200] [seed=1]\n\
  hdlean toy16 [cycles=60]\n\
FIFO is a verified two-entry skid buffer. Inputs: valid, ready, payload LSB first, reset.\n\
Outputs: ready, valid, payload LSB first. Counter inputs: enable, reset. Clock is implicit."

private def number (s : String) (max : Nat := 1000000) : Except String Nat := do
  let some n := s.toNat? | throw s!"invalid natural number: {s}"
  if n > max then throw s!"value exceeds limit {max}: {n}"
  return n

/-- Every design reaches the emitter as a node graph: tree circuits through the
proved `Circuit.toDag`, the CPU directly. -/
private def withDesign (name : String) (width : Nat)
    (f : {i r o : Nat} → Dag 0 i r o → IO Unit) : IO Unit := do
  match name with
  | "fifo" => f (Fifo.hardware width).toDag
  | "counter" => f Counter.hardware.toDag
  | "pipeline" => f (SkidBuffer.hardware width).toDag
  | "ring" => f (Fifo.Circular.Physical.hardware 4 width).toDag
  | "ram" => f (RAMCircuit.hardware 4 width).toDag
  | "toy16" => f (Toy16.DagPhysical.hardware Toy16.sumProgram)
  | _ => throw (IO.userError s!"unknown design: {name}")

private def parseFormat (format : String) : IO Proved.Format :=
  match format with
  | "sv" => pure .systemVerilog
  | "aiger" => pure .aiger
  | "rtlil" => pure .rtlil
  | _ => throw (IO.userError s!"unknown format: {format}; expected sv, aiger, rtlil")

private def parseNum (s : String) (max : Nat := 1000000) : IO Nat :=
  match number s max with | .ok n => pure n | .error e => throw (IO.userError e)

private def bools (a : Array Bool) : Lean.Json := .arr (a.map Lean.toJson)
private def traceJson (g : Graph) (rows : Array TraceRow) : Lean.Json := .arr (rows.map fun r => Lean.Json.mkObj
  [("cycle", Lean.toJson r.cycle), ("inputs", bools r.inputs), ("state", bools r.state),
   ("outputs", bools r.outputs), ("next", bools r.next),
   ("signals", if r.cycle == 0 then Lean.Json.mkObj
     [("inputs", Lean.toJson g.inputNames), ("state", Lean.toJson g.stateNames),
      ("outputs", Lean.toJson g.outputNames), ("next", Lean.toJson g.stateNames),
      ("sources", Lean.toJson g.sources)] else .null)])

private def writeFile (path : String) (content : String) : IO Unit := do
  let path := System.FilePath.mk path
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path content

/-- Write `emit c`, read the file back and decode it with the proved parser. The
generic theorem `Proved.emit_correct` says what `emit c` means; the read-back
guards the compiled code and the file write that produced these bytes. -/
private def emitChecked (f : Proved.Format) (c : Dag d i r o) (path : String) : IO Unit := do
  writeFile path (f.emit c)
  let bytes ← IO.FS.readFile (System.FilePath.mk path)
  match f.parse bytes with
  | some g =>
    unless g.graph.logic == c.lower.logic do
      throw (IO.userError s!"{path}: read-back graph differs from the circuit's lowering")
  | none => throw (IO.userError s!"{path}: the proved parser rejected the written file")

private def execute (args : List String) : IO Unit := do
  match args with
  | ["--help"] | ["help"] | [] => IO.println usage
  | ["--version"] => IO.println "HDLean 0.2.0 (Lean 4.35.0)"
  | "emit-async" :: format :: path :: rest =>
    if rest.length > 2 then throw (IO.userError usage)
    let width ← parseNum (rest[0]?.getD "8") 64
    let k ← parseNum (rest[1]?.getD "4") 8
    let f ← parseFormat format
    let c := (AsyncFifo.Physical.hardware k width).eventCircuit.toDag
    emitChecked f c path
    IO.println s!"Wrote {path}: event-encoded, the two clock edges are inputs after the payload and reset."
  | "emit" :: design :: format :: path :: rest =>
    if rest.length > 1 then throw (IO.userError usage)
    let width ← parseNum (rest.headD "8") 64
    let f ← parseFormat format
    withDesign design width fun c => do
      emitChecked f c path
      let g := c.lower
      IO.println s!"Wrote {path} ({g.ffBits} flip-flops, {g.andCount} AND gates; proved emitter, read back)."
  | "metrics" :: design :: rest =>
    if rest.length > 1 then throw (IO.userError usage)
    let width ← parseNum (rest.headD "8") 64
    withDesign design width fun c => do
      let g := c.lower
      IO.println (Lean.Json.mkObj [("design", .str g.name), ("ff_bits", Lean.toJson g.ffBits),
        ("memory_bits", Lean.toJson (0 : Nat)), ("and_gates", Lean.toJson g.andCount),
        ("logic_depth", Lean.toJson g.depth), ("physical_metrics", .null)]).pretty
  | "trace" :: design :: path :: rest =>
    if rest.length > 3 then throw (IO.userError usage)
    let width ← parseNum (rest[0]?.getD "8") 64
    let cycles ← parseNum (rest[1]?.getD "60") 10000
    let seed ← parseNum (rest[2]?.getD "1") 4294967295
    withDesign design width fun c => do
      let g := c.lower
      writeFile path (traceJson g (trace g cycles seed)).pretty
  | "check" :: design :: rest =>
    if rest.length > 3 then throw (IO.userError usage)
    let width ← parseNum (rest[0]?.getD "8") 64
    let cycles ← parseNum (rest[1]?.getD "200") 10000
    let seed ← parseNum (rest[2]?.getD "1") 4294967295
    withDesign design width fun c => match checkDag c cycles seed with
      | .ok _ => IO.println s!"PASS: {cycles} cycles, seed {seed}"
      | .error e => throw (IO.userError e)
  | "toy16" :: rest =>
    if rest.length > 1 then throw (IO.userError usage)
    let cycles ← parseNum (rest.headD "60") 1000
    let mut s : Toy16.CoreState := ⟨Toy16.ArchState.atReset (fun _ => 0xAAAA) (fun _ => 0x5555), 0, false⟩
    let m := Toy16.core Toy16.sumProgram
    IO.println "cycle,pc,instruction,next_pc,halt"
    for t in [:cycles] do
      if let some r := m.out s then IO.println s!"{t},{r.pc.toNat},{r.instr.toNat},{r.nextPc.toNat},{r.halt}"
      s := m.next s false
    IO.println s!"halted={s.arch.halted}, memory[0]={s.arch.dmem 0}"
  | _ => throw (IO.userError usage)

def main (args : List String) : IO UInt32 := do
  try execute args; return 0
  catch e => (← IO.getStderr).putStrLn s!"hdlean: {e}"; return 1
