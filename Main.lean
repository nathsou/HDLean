import HDLean
import Designs
import Lean
open HDLean HDLean.Backend HDLean.Verification

private def usage : String := "HDLean 0.2.0\n\
  hdlean emit <fifo|counter|pipeline|ram|ring|toy16> <sv|aiger|rtlil> <path> [width=8]\n\
  hdlean emit-async <sv|rtlil|aiger> <path> [width=8] [log2depth=4]\n\
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

private def withDesign (name : String) (width : Nat)
    (f : {i r o : Nat} → Circuit 0 i r o → IO Unit) : IO Unit := do
  match name with
  | "fifo" => f (Fifo.hardware width)
  | "counter" => f Counter.hardware
  | "pipeline" => f (SkidBuffer.hardware width)
  | "ring" => f (Fifo.Circular.Physical.hardware 4 width)
  | "ram" => f (RAMCircuit.hardware 4 width)
  | "toy16" => f (Toy16.Physical.hardware Toy16.sumProgram)
  | _ => throw (IO.userError s!"unknown design: {name}")

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

private def execute (args : List String) : IO Unit := do
  match args with
  | ["--help"] | ["help"] | [] => IO.println usage
  | ["--version"] => IO.println "HDLean 0.2.0 (Lean 4.35.0)"
  | "emit-async" :: format :: path :: rest =>
    if rest.length > 2 then throw (IO.userError usage)
    let width ← parseNum (rest[0]?.getD "8") 64
    let k ← parseNum (rest[1]?.getD "4") 8
    let c := AsyncFifo.Physical.hardware k width
    if format == "aiger" then
      let artifact ← match Backend.checkedPrint .aiger c.eventCircuit with
        | .ok a => pure a | .error e => throw (IO.userError e)
      writeFile path artifact.text
      IO.println s!"Wrote event-encoded {path}; independent edge inputs represent both physical clocks."
    else
      let f ← match format with
        | "sv" => pure MultiClock.Format.systemVerilog
        | "rtlil" => pure MultiClock.Format.rtlil
        | _ => throw (IO.userError "expected sv, rtlil, or aiger")
      let artifact ← match MultiClock.checkedPrint f c with
        | .ok a => pure a | .error e => throw (IO.userError e)
      writeFile path artifact.text
      IO.println s!"Wrote {path} with native clk_0 and clk_1 ports."
  | "emit" :: "toy16" :: format :: path :: rest =>
    if rest.length > 1 then throw (IO.userError usage)
    let _ ← parseNum (rest.headD "8") 64
    let f ← match format with
      | "sv" => pure Proved.Format.systemVerilog
      | "aiger" => pure Proved.Format.aiger
      | "rtlil" => pure Proved.Format.rtlil
      | _ => throw (IO.userError s!"unknown format: {format}; expected sv, aiger, rtlil")
    let c := Toy16.DagPhysical.hardware Toy16.sumProgram
    writeFile path (f.emit c)
    IO.println s!"Wrote {path} ({c.lower.latches} flip-flops, {c.lower.gates.size} AND gates; generic proved emitter)."
  | "emit" :: design :: format :: path :: rest =>
    if rest.length > 1 then throw (IO.userError usage)
    let width ← parseNum (rest.headD "8") 64
    withDesign design width fun c => do
      let format ← match format with
        | "sv" => pure Format.systemVerilog
        | "aiger" => pure Format.aiger
        | "rtlil" => pure Format.rtlil
        | _ => throw (IO.userError s!"unknown format: {format}; expected sv, aiger, rtlil")
      let artifact ← match checkedPrint format c with
        | .ok a => pure a
        | .error e => throw (IO.userError e)
      let graph := compileCandidate c
      writeFile path artifact.text
      IO.println s!"Wrote {path} ({graph.ffBits} flip-flops, {graph.andCount} AND gates)."
  | "metrics" :: design :: rest =>
    if rest.length > 1 then throw (IO.userError usage)
    let width ← parseNum (rest.headD "8") 64
    withDesign design width fun c => do
      let g := compileCandidate c
      IO.println (Lean.Json.mkObj [("design", .str g.name), ("ff_bits", Lean.toJson g.ffBits),
        ("memory_bits", Lean.toJson (0 : Nat)), ("and_gates", Lean.toJson g.andCount),
        ("logic_depth", Lean.toJson g.depth), ("physical_metrics", .null)]).pretty
  | "trace" :: design :: path :: rest =>
    if rest.length > 3 then throw (IO.userError usage)
    let width ← parseNum (rest[0]?.getD "8") 64
    let cycles ← parseNum (rest[1]?.getD "60") 10000
    let seed ← parseNum (rest[2]?.getD "1") 4294967295
    withDesign design width fun c => do
      let g := compileCandidate c
      writeFile path (traceJson g (trace g cycles seed)).pretty
  | "check" :: design :: rest =>
    if rest.length > 3 then throw (IO.userError usage)
    let width ← parseNum (rest[0]?.getD "8") 64
    let cycles ← parseNum (rest[1]?.getD "200") 10000
    let seed ← parseNum (rest[2]?.getD "1") 4294967295
    withDesign design width fun c => match checkCircuit c cycles seed with
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
