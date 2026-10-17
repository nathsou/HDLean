import HDLean
import Designs
import Designs.Euler
import Lean
open HDLean HDLean.Backend HDLean.Verification

private def usage : String := "HDLean 0.3.0\n\
  Single-clock designs: counter, fifo, pipeline, ring (2^4 words), ram (16 words), toy16, ops.\n\
  The multi-clock design async (dual-clock FIFO, 2^4 words) is emitted word-level only.\n\
  hdlean emit <design> <sv|aiger|rtlil> <path> [width=8]   (bit-blasted by the proved Design.toDag)\n\
  hdlean abc-emit <design> <sv|aiger|rtlil> <path> [width=8]  (ABC-optimised, checked by a verified LRAT certificate)\n\
  hdlean metrics <design> [width=8]\n\
  hdlean trace <design> <path.json> [width=8] [cycles=60] [seed=1]\n\
  hdlean check <design> [width=8] [cycles=200] [seed=1]\n\
  hdlean rtl-emit <design|async> <path.sv|path.il> [width=8]  (word-level SystemVerilog or RTLIL, read back)\n\
  hdlean rtl-trace <design|async> <path.json> [width=8] [cycles=100] [seed=1]\n\
  hdlean rtl-metrics <design> [width=8]\n\
  hdlean toy16 [cycles=60]     (retirement reports of the word-level CPU running the sum program)\n\
  hdlean review <path.md>      (challenge statements, axioms, interfaces, scenarios; run under `lake env`)\n\
  hdlean euler-list            (the Project Euler solvers, as JSON)\n\
  hdlean euler-sim <n>         (run solver n in Lean from reset to done; compare with the Lean reference)\n\
  hdlean euler-ref <n>         (the answer from the plain-Lean reference)\n\
  hdlean euler-emit <n> <dir> <report-clock-hz>  (solver, cycle counter and UART reporter as word-level SystemVerilog, read back)\n\
Inputs and outputs are the ports of each design's top module; reset is the last bit-level input.\n\
Width applies to fifo, pipeline, ring, ram and async."

private def number (s : String) (max : Nat := 1000000) : Except String Nat := do
  let some n := s.toNat? | throw s!"invalid natural number: {s}"
  if n > max then throw s!"value exceeds limit {max}: {n}"
  return n

/-- Single-clock word-level designs. -/
private def rtlDesign (name : String) (width : Nat := 8) : IO Rtl.Design :=
  match name with
  | "counter" => pure Counter.Word.design
  | "fifo" => pure (Fifo.Word.design width)
  | "pipeline" => pure (SkidBuffer.Word.design width)
  | "ring" => pure (Fifo.Circular.Word.design 4 width)
  | "ram" => pure (RAM.Word.design 4 width)
  | "toy16" => pure Toy16.Word.design
  | "ops" => pure RtlOps.design
  | "async" => throw (IO.userError "async is a multi-clock design: use rtl-emit or rtl-trace")
  | _ => throw (IO.userError s!"unknown design: {name}")

/-- Bit-blast a word-level design with the proved `Design.toDag`, after the proved
word-level pass (`Design.optimized_step`/`optimized_output`: same cycle semantics). -/
private def withRtl (d : Rtl.Design) (f : {i r o : Nat} → Dag 0 i r o → IO Unit) : IO Unit :=
  match d.optimized.toDag with
  | some g => f g
  | none => throw (IO.userError "bit-blasting failed: the design does not pass the blaster's width checks")

/-- Every design reaches the bit-level emitters as a node graph, through the
proved `Design.toDag`. -/
private def withDesign (name : String) (width : Nat)
    (f : {i r o : Nat} → Dag 0 i r o → IO Unit) : IO Unit := do
  withRtl (← rtlDesign name width) f

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
    unless g.graph.logic == (Dag.lowerOpt c).logic do
      throw (IO.userError s!"{path}: read-back graph differs from the circuit's lowering")
  | none => throw (IO.userError s!"{path}: the proved parser rejected the written file")

/-- Optimise the lowering of `c` with ABC, then validate: Lean builds the miter of
the two graphs, CaDiCaL refutes it, Lean's verified LRAT checker checks the
refutation. `Validate.select` falls back to our graph on any failure, so the
external tools are untrusted. -/
private def abcOptimize (c : Dag d i r o) (work : System.FilePath) :
    IO (Graph × Array Std.Tactic.BVDecide.LRAT.IntAction × String) := do
  IO.FS.createDirAll work
  let g := Dag.lowerOpt c
  let abc := (← IO.getEnv "HDLEAN_ABC").getD "yosys-abc"
  -- Lean ships CaDiCaL next to `lean` (it is what `bv_decide` uses).
  let cadical ← match ← IO.getEnv "HDLEAN_CADICAL" with
    | some c => pure c
    | none => do
      let r ← IO.Process.output { cmd := "lean", args := #["--print-prefix"] }
      let c := System.FilePath.mk r.stdout.trimAscii.toString / "bin" / "cadical"
      pure (if r.exitCode == 0 && (← c.pathExists) then c.toString else "cadical")
  let script := (← IO.getEnv "HDLEAN_ABC_SCRIPT").getD "strash; dc2; fraig; dc2; drw; drf; dc2"
  let inPath := work / "in.aig"
  let outPath := work / "out.aig"
  IO.FS.writeBinFile inPath (AigerBinary.write g)
  let t0 ← IO.monoMsNow
  let r ← IO.Process.output { cmd := abc, args := #["-q", s!"read_aiger {inPath}; {script}; write_aiger {outPath}"] }
  if r.exitCode != 0 then return (g, #[], s!"ABC failed: {r.stderr}")
  let t1 ← IO.monoMsNow
  let some p := AigerBinary.read (← IO.FS.readBinFile outPath) | return (g, #[], "ABC output not readable")
  let h := p.graph g
  let some e := Validate.miter g (Validate.adopt g h) | return (g, #[], "ports changed; not validated")
  let cnfPath := work / "miter.cnf"
  let proofPath := work / "miter.lrat"
  IO.FS.writeFile cnfPath (Std.Sat.CNF.dimacs (Std.Sat.AIG.toCNF e))
  let t2 ← IO.monoMsNow
  let s ← IO.Process.output
    { cmd := cadical, args := #[cnfPath.toString, proofPath.toString, "--binary", "--quiet", "--lrat", "--unsat"] }
  if s.exitCode != 20 then return (g, #[], s!"the SAT solver did not refute the miter (exit {s.exitCode})")
  let t3 ← IO.monoMsNow
  let cert ← Std.Tactic.BVDecide.LRAT.loadLRATProof proofPath
  let ok := Validate.select g h cert
  let t4 ← IO.monoMsNow
  let accepted := ok.gates.size == p.gates.size && ok.next == p.next
  let msg := if accepted then
      s!"ABC {g.andCount} → {p.gates.size} AND gates; validated (ABC {t1 - t0} ms, miter {t2 - t1} ms, SAT {t3 - t2} ms, verified LRAT check {t4 - t3} ms)"
    else "certificate rejected; emitted the unoptimised graph"
  return (h, cert, msg)

/-- Write `emitWith c h cert` and read it back, as `emitChecked` does. -/
private def emitWithChecked (f : Proved.Format) (c : Dag d i r o) (h : Graph)
    (cert : Array Std.Tactic.BVDecide.LRAT.IntAction) (path : String) : IO Unit := do
  writeFile path (f.emitWith c h cert)
  let bytes ← IO.FS.readFile (System.FilePath.mk path)
  match f.parse bytes with
  | some g =>
    unless g.graph.logic == (Validate.select (Dag.lowerOpt c) h cert).logic do
      throw (IO.userError s!"{path}: read-back graph differs from the selected graph")
  | none => throw (IO.userError s!"{path}: the proved parser rejected the written file")

/-- Hierarchical names of every register and memory of module `k`, with memory depths. -/
private partial def statePaths (d : Rtl.Design) (k : Nat) (pre : String) : List (String × Nat) :=
  match d.modules[k]? with
  | none => []
  | some m =>
    let regs := (m.regs.toList.zipIdx).map fun (r, i) => (s!"{pre}r_{i}_{r.name}", 0)
    let mems := (m.mems.toList.zipIdx).map fun (mm, i) => (s!"{pre}m_{i}_{mm.name}", 2 ^ mm.addrWidth)
    let subs := (m.cells.toList.zipIdx).flatMap fun (c, i) => match c.op with
      | .inst j _ _ => if j < k then statePaths d j s!"{pre}u_{i}." else []
      | _ => []
    regs ++ mems ++ subs

/-- A word-level trace from the all-zero store: random input words, reset at cycle 0
and now and then. Outputs are read before the clock edge. -/
private def rtlTrace (d : Rtl.Design) (cycles seed : Nat) : Lean.Json := Id.run do
  let m := d.modules[d.top]?.getD default
  let mut st : Rtl.Store := default
  let mut seed := seed
  let mut rows : Array Lean.Json := #[]
  for t in [:cycles] do
    let mut ins : Array Nat := #[]
    for p in m.inputs do
      seed := (seed * 1103515245 + 12345) % 2147483648
      let hi := seed
      seed := (seed * 1103515245 + 12345) % 2147483648
      ins := ins.push ((hi * 2147483648 + seed) % 2 ^ p.width)
    seed := (seed * 1103515245 + 12345) % 2147483648
    let rst := t == 0 || seed % 23 == 0
    let outs := d.output st ins
    rows := rows.push (Lean.Json.mkObj [("cycle", Lean.toJson t), ("inputs", Lean.toJson ins),
      ("rst", Lean.toJson rst), ("outputs", Lean.toJson outs)])
    st := d.step st (ins, rst)
  let top := m.name.text
  return Lean.Json.mkObj [
    ("module", .str s!"hd_{d.top}_{top}"),
    ("inputs", Lean.toJson (m.inputs.toList.zipIdx.map fun (p, i) => Lean.Json.mkObj
      [("name", .str s!"i_{i}_{p.name}"), ("width", Lean.toJson p.width)])),
    ("outputs", Lean.toJson (m.outputs.toList.zipIdx.map fun (o, i) => Lean.Json.mkObj
      [("name", .str s!"o_{i}_{o.name}"), ("width", Lean.toJson (m.cellWidth o.node))])),
    ("state", Lean.toJson ((statePaths d d.top "").map fun (n, depth) => Lean.Json.mkObj
      [("path", .str n), ("depth", Lean.toJson depth)])),
    ("rows", .arr rows)]

/-- A multi-clock trace from the all-zero state: random clock edges, inputs and
resets (an edge with reset in both domains on the first two steps), synchronizers sampling
the old source value (as two simultaneous edges do in an event simulator).
Outputs are read before the edges. -/
private def asyncTrace (md : Rtl.MDesign) (cycles seed : Nat) : Lean.Json := Id.run do
  let mut s : Rtl.MDesign.State := ⟨#[default, default], #[0, 0], #[0, 0], #[#[]]⟩
  let mut seed := seed
  let mut rows : Array Lean.Json := #[]
  let draw := fun (seed : Nat) => (seed * 1103515245 + 12345) % 2147483648
  for t in [:cycles] do
    let mut ins : Array (Array Nat) := #[]
    for d in [0, 1] do
      let m := md.topModule d
      let mut x : Array Nat := #[]
      for p in (m.inputs.toList.drop 1).take (md.nExt d) do
        seed := draw seed
        x := x.push (seed % 2 ^ p.width)
      ins := ins.push x
    seed := draw seed
    let edges := #[t < 2 || seed % 3 != 0, t < 2 || seed / 3 % 3 != 0]
    seed := draw seed
    let rsts := #[t < 2 || seed % 29 == 0, t < 2 || seed / 29 % 31 == 0]
    let masks := md.crossings.map fun c => 2 ^ (md.regOut c.src c.out).2 - 1
    let e : Rtl.MDesign.Event := ⟨ins, rsts, edges, masks⟩
    let outs := (List.range md.tops.size).toArray.map (md.outputs s e)
    rows := rows.push (Lean.Json.mkObj [("step", Lean.toJson t), ("edges", Lean.toJson edges),
      ("resets", Lean.toJson rsts), ("inputs", Lean.toJson ins), ("outputs", Lean.toJson outs)])
    s := md.next s e
  let ports := (List.range md.tops.size).map fun d =>
    let m := md.topModule d
    Lean.Json.mkObj [("inputs", Lean.toJson (((m.inputs.toList.drop 1).take (md.nExt d)).map (·.width))),
      ("outputs", Lean.toJson (m.outputs.toList.map fun o => m.cellWidth o.node))]
  return Lean.Json.mkObj [("module", .str "hd_mtop"), ("domains", Lean.toJson ports),
    ("memories", Lean.toJson (md.mems.toList.map fun mm => 2 ^ mm.addrWidth)), ("rows", .arr rows)]

private unsafe def enableInitUnsafe : IO Unit := Lean.enableInitializersExecution
/-- Notation and pretty-printer extensions of imported modules are registered by initializers. -/
@[implemented_by enableInitUnsafe] private opaque enableInit : IO Unit

private def execute (args : List String) : IO Unit := do
  match args with
  | ["--help"] | ["help"] | [] => IO.println usage
  | ["--version"] => IO.println "HDLean 0.3.0 (Lean 4.35.0)"
  | "emit" :: design :: format :: path :: rest =>
    if rest.length > 1 then throw (IO.userError usage)
    let width ← parseNum (rest.headD "8") 64
    let f ← parseFormat format
    withDesign design width fun c => do
      emitChecked f c path
      let g := Dag.lowerOpt c
      IO.println s!"Wrote {path} ({g.ffBits} flip-flops, {g.andCount} AND gates; proved emitter, read back)."
  | "abc-emit" :: design :: format :: path :: rest =>
    if rest.length > 1 then throw (IO.userError usage)
    let width ← parseNum (rest.headD "8") 64
    let f ← parseFormat format
    withDesign design width fun c => do
      let work := (System.FilePath.mk path).withExtension "abc"
      let (h, cert, msg) ← abcOptimize c work
      emitWithChecked f c h cert path
      IO.println s!"Wrote {path}: {msg}."
  | "metrics" :: design :: rest =>
    if rest.length > 1 then throw (IO.userError usage)
    let width ← parseNum (rest.headD "8") 64
    withDesign design width fun c => do
      let g := Dag.lowerOpt c
      IO.println (Lean.Json.mkObj [("design", .str g.name), ("ff_bits", Lean.toJson g.ffBits),
        ("memory_bits", Lean.toJson (0 : Nat)), ("and_gates", Lean.toJson g.andCount),
        ("logic_depth", Lean.toJson g.depth), ("physical_metrics", .null)]).pretty
  | "trace" :: design :: path :: rest =>
    if rest.length > 3 then throw (IO.userError usage)
    let width ← parseNum (rest[0]?.getD "8") 64
    let cycles ← parseNum (rest[1]?.getD "60") 10000
    let seed ← parseNum (rest[2]?.getD "1") 4294967295
    withDesign design width fun c => do
      let g := Dag.lowerOpt c
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
    let imem := Toy16.sumProgram
    let mut st : Rtl.Store := default
    IO.println "cycle,pc,instruction,next_pc,halt"
    for t in [:cycles] do
      let r := Toy16.Word.observe (Rtl.Bundle.decode Toy16.Word.CpuOut
        ((Toy16.Word.design.output st (Toy16.Word.fetch imem st)).getD · 0))
      if let some r := r then IO.println s!"{t},{r.pc.toNat},{r.instr.toNat},{r.nextPc.toNat},{r.halt}"
      st := Toy16.Word.design.step st (Toy16.Word.fetch imem st, t == 0)
  | "rtl-emit" :: "async" :: path :: rest =>
    if rest.length > 1 then throw (IO.userError usage)
    let width ← parseNum (rest.headD "8") 64
    let md := AsyncFifo.Word.design 4 width
    unless md.check do throw (IO.userError "async does not pass MDesign.check")
    let rtlil := path.endsWith ".il"
    writeFile path (if rtlil then md.rtlil else md.systemVerilog)
    let bytes ← IO.FS.readFile (System.FilePath.mk path)
    let back := if rtlil then Rtl.MDesign.parseRTLIL bytes else Rtl.MDesign.parseSystemVerilog bytes
    unless back == some md do
      throw (IO.userError s!"{path}: the proved parser did not read back the design")
    let fmt := if rtlil then "RTLIL" else "SystemVerilog"
    IO.println s!"Wrote {path}: word-level {fmt}, {md.tops.size} clock domains, {md.crossings.size} synchronizers, {md.mems.size} shared memory; proved round trip, read back."
  | "rtl-emit" :: design :: path :: rest =>
    if rest.length > 1 then throw (IO.userError usage)
    let width ← parseNum (rest.headD "8") 64
    let d0 ← rtlDesign design width
    unless d0.check do throw (IO.userError s!"{design} does not pass Design.check")
    -- The proved word-level pass: same `step` and `output` as the design.
    let d := d0.optimized
    -- `.il` selects word-level RTLIL, anything else word-level SystemVerilog; both are read back.
    let rtlil := path.endsWith ".il"
    writeFile path (if rtlil then d.rtlil else d.systemVerilog)
    let bytes ← IO.FS.readFile (System.FilePath.mk path)
    let back := if rtlil then Rtl.Design.parseRTLIL bytes else Rtl.Design.parseSystemVerilog bytes
    unless back == some d do
      throw (IO.userError s!"{path}: the proved parser did not read back the design")
    let cells := d.modules.toList.foldl (fun n m => n + m.cells.size) 0
    let cells0 := d0.modules.toList.foldl (fun n m => n + m.cells.size) 0
    let fmt := if rtlil then "RTLIL" else "SystemVerilog"
    IO.println s!"Wrote {path}: word-level {fmt}, {d.modules.size} modules, {cells} cells ({cells0} before the proved word-level passes); proved round trip, read back."
  | "rtl-trace" :: "async" :: path :: rest =>
    if rest.length > 3 then throw (IO.userError usage)
    let width ← parseNum (rest[0]?.getD "8") 64
    let cycles ← parseNum (rest[1]?.getD "100") 100000
    let seed ← parseNum (rest[2]?.getD "1") 4294967295
    writeFile path (asyncTrace (AsyncFifo.Word.design 4 width) cycles seed).pretty
  | "rtl-trace" :: design :: path :: rest =>
    if rest.length > 3 then throw (IO.userError usage)
    let width ← parseNum (rest[0]?.getD "8") 64
    let cycles ← parseNum (rest[1]?.getD "100") 100000
    let seed ← parseNum (rest[2]?.getD "1") 4294967295
    writeFile path (rtlTrace (← rtlDesign design width) cycles seed).pretty
  | ["review", path] =>
    Lean.initSearchPath (← Lean.findSysroot)
    enableInit
    let env ← Lean.importModules #[{ module := `Designs }] {} (trustLevel := 1024) (loadExts := true)
    writeFile path (← Review.render env)
    IO.println s!"Wrote {path}."
  | "rtl-metrics" :: design :: rest =>
    if rest.length > 1 then throw (IO.userError usage)
    let width ← parseNum (rest.headD "8") 64
    let d ← rtlDesign design width
    let regBits := d.modules.toList.foldl (fun n m => n + (m.regs.toList.map Rtl.Reg.width).sum) 0
    let memBits := d.modules.toList.foldl (fun n m =>
      n + (m.mems.toList.map fun mm => 2 ^ mm.addrWidth * mm.width).sum) 0
    let cells := d.modules.toList.foldl (fun n m => n + m.cells.size) 0
    withRtl d fun g => do
      let lg := Dag.lowerOpt g
      IO.println (Lean.Json.mkObj [("design", .str design), ("modules", Lean.toJson d.modules.size),
        ("cells", Lean.toJson cells),
        ("cells_optimized", Lean.toJson (d.optimized.modules.toList.foldl (fun n m => n + m.cells.size) 0)),
        ("register_bits", Lean.toJson regBits), ("memory_bits", Lean.toJson memBits),
        ("blasted_state_bits", Lean.toJson lg.ffBits), ("blasted_and_gates", Lean.toJson lg.andCount),
        ("blasted_logic_depth", Lean.toJson lg.depth)]).pretty
  | ["euler-list"] =>
    IO.println (Lean.toJson (Euler.problems.map fun p => Lean.Json.mkObj [("number", Lean.toJson p.number),
      ("title", .str p.title), ("idea", .str p.idea), ("answer_width", Lean.toJson p.answerWidth),
      ("max_cycles", Lean.toJson p.maxCycles)])).pretty
  | ["euler-sim", n] =>
    let some p := Euler.find? (← parseNum n) | throw (IO.userError s!"no solver for problem {n}")
    let reference := p.reference ()
    match Euler.simulate p.design.optimized p.maxCycles with
    | some (cycles, answer) =>
      IO.println (Lean.Json.mkObj [("number", Lean.toJson p.number), ("cycles", Lean.toJson cycles),
        ("answer", Lean.toJson answer), ("reference", Lean.toJson reference),
        ("ok", Lean.toJson (answer == reference))]).compress
      unless answer == reference do throw (IO.userError s!"problem {n}: design answered {answer}, reference {reference}")
    | none => throw (IO.userError s!"problem {n}: no answer within {p.maxCycles} cycles")
  | ["euler-ref", n] =>
    let some p := Euler.find? (← parseNum n) | throw (IO.userError s!"no solver for problem {n}")
    IO.println (Lean.Json.mkObj [("number", Lean.toJson p.number), ("reference", Lean.toJson (p.reference ()))]).compress
  | ["euler-emit", n, dir, hz] =>
    let some p := Euler.find? (← parseNum n) | throw (IO.userError s!"no solver for problem {n}")
    let clock ← parseNum hz 1000000000
    let divisor := (clock + 57600) / 115200
    let solver := p.design.optimized
    let report := (Euler.Report.design divisor).optimized
    let count := Euler.Report.countDesign.optimized
    unless solver.check do throw (IO.userError s!"problem {n}: the solver does not pass Design.check")
    unless report.check && count.check do throw (IO.userError "the reporter does not pass Design.check")
    for (d, file) in [(solver, "solver.sv"), (report, "report.sv"), (count, "count.sv")] do
      let path := (System.FilePath.mk dir / file).toString
      writeFile path d.systemVerilog
      unless Rtl.Design.parseSystemVerilog (← IO.FS.readFile path) == some d do
        throw (IO.userError s!"{path}: the proved parser did not read back the design")
    let m := solver.modules[solver.top]!
    IO.println (Lean.Json.mkObj [("module", .str s!"hd_{solver.top}_{m.name.text}"),
      ("answer_width", Lean.toJson p.answerWidth), ("divisor", Lean.toJson divisor),
      ("cells", Lean.toJson m.cells.size)]).compress
  | _ => throw (IO.userError usage)

def main (args : List String) : IO UInt32 := do
  try execute args; return 0
  catch e => (← IO.getStderr).putStrLn s!"hdlean: {e}"; return 1
