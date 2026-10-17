import Lean
import Designs.Counter.Challenge
import Designs.Fifo.Challenge
import Designs.CircularFifo.Challenge
import Designs.SkidBuffer.Challenge
import Designs.AsyncFifo.Challenge
import Designs.Toy16.Challenge
import Designs.RAM.Challenge
import Designs.Toy16.Programs

/-!
# Review documents

`hdlean review` writes what a human reviewer needs to accept a challenge
without reading proofs: each theorem's statement as Lean prints it, its
documentation, the axioms its proof depends on, the interface of word-level
designs (ports, registers with their resets, memories, instances), and
scenario tables computed by running both the specification and the design.
-/
namespace HDLean.Review
open Lean HDLean.Rtl

/-- Challenge theorems, in reading order. -/
def challenges : List (Name × String) :=
  [(`HDLean.Toy16.Challenge.correctness, "Toy16: retirement refines the ISA"),
   (`HDLean.RAM.Challenge.correctness, "Single-port RAM on the memory primitive"),
   (`HDLean.Counter.Challenge.correctness, "Decade counter"),
   (`HDLean.Counter.Challenge.budget, "Decade counter: state bits"),
   (`HDLean.Fifo.Challenge.correctness, "Two-entry FIFO"),
   (`HDLean.Fifo.Challenge.budget, "Two-entry FIFO: state bits"),
   (`HDLean.CircularFifo.Challenge.correctness, "General-depth FIFO on a memory"),
   (`HDLean.CircularFifo.Challenge.budget, "General-depth FIFO: state bits"),
   (`HDLean.SkidBuffer.Challenge.correctness, "Three-stage pipeline"),
   (`HDLean.SkidBuffer.Challenge.budget, "Three-stage pipeline: state bits"),
   (`HDLean.AsyncFifo.Challenge.correctness, "Dual-clock FIFO (two clock domains)"),
   (`HDLean.AsyncFifo.Challenge.enqueue_progress, "Dual-clock FIFO: writes complete"),
   (`HDLean.AsyncFifo.Challenge.dequeue_progress, "Dual-clock FIFO: reads complete")]

def mdEscape (s : String) : String := s.replace "|" "\\|"

def coreCtx : Core.Context :=
  let opts : Options := Options.empty.set `format.width (100 : Nat)
  let opens := [`HDLean, `HDLean.Rtl, `HDLean.Toy16, `HDLean.Toy16.Word, `HDLean.RAM.Word].map
    fun n => OpenDecl.simple n []
  { fileName := "<review>", fileMap := default, options := opts, openDecls := opens }

/-- The project definitions a statement mentions, with their bodies when short:
what a reviewer must read to know what the theorem says. -/
def vocabulary (env : Environment) (n : Name) : IO String := do
  let some ci := env.find? n | return ""
  let internal := fun c : Name => match c with
    | .str _ last => last.startsWith "inst" || last.startsWith "match_" || last.startsWith "_" || last == "proof_1"
    | _ => true
  let keep := fun c : Name => (`HDLean).isPrefixOf c && !(env.find? c |>.any (·.isCtor)) && c != n &&
    !internal c && !c.isInternalDetail && !env.isProjectionFn c &&
    !(env.find? c |>.any fun ci => ci matches .thmInfo _)
  let first := ci.type.getUsedConstants.filter keep
  -- one more level: what the definitions in the statement are made of
  let mut used := first
  for c in first do
    if let some v := (env.find? c).bind (·.value?) then
      for c' in v.getUsedConstants do
        if keep c' && !used.contains c' then used := used.push c'
  let s : Core.State := { env }
  let mut out := ""
  for c in used do
    let some cc := env.find? c | continue
    let (sig, _, _) ← (PrettyPrinter.ppSignature c).toIO coreCtx s
    let doc ← findDocString? env c
    out := out ++ s!"- `{toString sig.fmt}`"
    if let some d := doc then out := out ++ s!" — {d.trimAscii.toString.replace "\n" " "}"
    out := out ++ "\n"
    if let some v := cc.value? then
      let (body, _, _) ← (PrettyPrinter.ppExpr v).toIO coreCtx s
      let text := toString body
      if text.length < 1200 then
        out := out ++ "\n  ```lean\n  " ++ text.replace "\n" "\n  " ++ "\n  ```\n"
  return out

/-- Statement, documentation and axioms of a declaration. -/
def describe (env : Environment) (n : Name) : IO (String × Option String × Array Name) := do
  let opts : Options := Options.empty.set `format.width (100 : Nat)
  let opens := [`HDLean, `HDLean.Rtl, `HDLean.Toy16, `HDLean.Toy16.Word, `HDLean.RAM.Word].map
    fun n => OpenDecl.simple n []
  let ctx : Core.Context := { fileName := "<review>", fileMap := default, options := opts, openDecls := opens }
  let s : Core.State := { env }
  let (sig, _, _) ← (PrettyPrinter.ppSignature n).toIO ctx s
  let (axs, _) ← (collectAxioms n : CoreM (Array Name)).toIO ctx s
  let doc ← findDocString? env n
  return (toString sig.fmt, doc, axs)

/-! ## Interfaces of word-level designs -/

def resetText : Reset → String
  | .none => "none (free-running)"
  | .sync v => s!"synchronous to {v}"

def moduleTable (d : Design) (k : Nat) (m : Rtl.Module) : String := Id.run do
  let mut out := s!"#### Module {k}: `{m.name}`\n\n| kind | name | width | detail |\n|---|---|---|---|\n"
  for p in m.inputs do
    out := out ++ s!"| input | `{p.name}` | {p.width} | |\n"
  for o in m.outputs do
    out := out ++ s!"| output | `{o.name}` | {m.cellWidth o.node} | cell {o.node} |\n"
  for r in m.regs do
    out := out ++ s!"| register | `{r.name}` | {r.width} | reset {resetText r.reset} |\n"
  for mm in m.mems do
    out := out ++ s!"| memory | `{mm.name}` | {mm.width} | {2 ^ mm.addrWidth} words, {mm.writes.size} write port(s), never reset |\n"
  for c in m.cells do
    match c.op with
    | .inst j _ _ =>
      let name := (d.modules[j]?.map (·.name.text)).getD "?"
      out := out ++ s!"| instance | `{name}` | {c.width} | module {j} |\n"
    | _ => pure ()
  return out ++ s!"\n{m.cells.size} cells.\n\n"

def designTables (d : Design) : String :=
  (d.modules.toList.zipIdx.map fun (m, k) => moduleTable d k m).foldl (· ++ ·) ""

/-! ## Scenarios -/

def bits (x : BitVec w) : String := toString x.toNat

def retireText (r : Toy16.Retire) : String :=
  let wb := match r.wb with | some (rd, v) => s!"r{rd.toNat} ← {v.toNat}" | none => ""
  let st := match r.store with | some (a, v) => s!"[{a.toNat}] ← {v.toNat}" | none => ""
  s!"| {r.pc.toNat} | 0x{String.ofList (Nat.toDigits 16 r.instr.toNat)} | {r.nextPc.toNat} | {wb} | {st} | {r.halt} |"

/-- The ISA's retirement stream and the design's reports on the sum program. -/
def toy16Scenario : String := Id.run do
  let imem := Toy16.sumProgram
  let s0 := Toy16.ArchState.atReset (fun _ => 0) (fun _ => 0)
  let mut out := "#### Scenario: the sum program (5+4+3+2+1, store, halt)\n\n" ++
    "Reference: `isaRetire sumProgram` from zeroed registers and memory.\n\n" ++
    "| # | pc | instr | next pc | write-back | store | halt |\n|---|---|---|---|---|---|---|\n"
  let mut n := 0
  while n < 23 do
    let r := Toy16.isaRetire imem s0 n
    out := out ++ s!"| {n} " ++ retireText r ++ "\n"
    n := n + 1
  out := out ++ "\nDesign: `Toy16.Word.design` in the closed loop, reset at cycle 0, all-zero power-up store; " ++
    "each report as it appears on the outputs.\n\n" ++
    "| cycle | pc | instr | next pc | write-back | store | halt |\n|---|---|---|---|---|---|---|\n"
  let mut st : Store := default
  for t in [:30] do
    let r := Toy16.Word.observe (Bundle.decode Toy16.Word.CpuOut
      ((Toy16.Word.design.output st (Toy16.Word.fetch imem st)).getD · 0))
    if let some r := r then out := out ++ s!"| {t} " ++ retireText r ++ "\n"
    st := Toy16.Word.design.step st (Toy16.Word.fetch imem st, t == 0)
  return out ++ "\n"

/-- Writes and reads on a 16 × 8 RAM: request, reference read word, design read word. -/
def ramScenario : String := Id.run do
  let a := 4; let w := 8
  let reqs : List (Nat × Nat × Nat) := [(1, 2, 7), (1, 5, 9), (0, 2, 0), (1, 2, 11), (0, 2, 0), (0, 5, 0), (0, 3, 0)]
  let mut st : Store := default
  let mut ref := RAM.Word.decode a w st
  let mut out := "#### Scenario: read-before-write on a 16 × 8 RAM, all-zero power-up\n\n" ++
    "| cycle | we | addr | wdata | reference read word | design read word |\n|---|---|---|---|---|---|\n"
  let mut t := 0
  for (we, addr, data) in reqs do
    let ins := #[we, addr, data]
    let hw := bv w (((RAM.Word.design a w).output st ins).getD 0 0)
    out := out ++ s!"| {t} | {we} | {addr} | {data} | {(HDLean.ram (2 ^ a) w).out ref |>.toNat} | {hw.toNat} |\n"
    ref := (HDLean.ram (2 ^ a) w).next ref (RAM.Word.request a w ins)
    st := (RAM.Word.design a w).step st (ins, false)
    t := t + 1
  return out ++ "\n"

/-- A decade counter run: enable, reference count, design output. -/
def counterScenario : String := Id.run do
  let ens := [true, true, false, true, true, true, true, true, true, true, true, false, true]
  let mut st : Store := default
  st := Counter.Word.design.step st (#[0], true)
  let mut n := Counter.Word.wordSpec.init
  let mut out := "#### Scenario: after one reset cycle\n\n| cycle | en | reference | design |\n|---|---|---|---|\n"
  let mut t := 1
  for en in ens do
    let ins := #[en.toNat]
    out := out ++ s!"| {t} | {en} | {Counter.Word.wordSpec.out n} | {Counter.Word.value (Counter.Word.design.output st ins)} |\n"
    n := Counter.Word.wordSpec.next n ins
    st := Counter.Word.design.step st (ins, false)
    t := t + 1
  return out ++ "\n"

def outputText (o : Fifo.Output (BitVec w)) : String :=
  s!"{o.enqReady} / {o.deqValid} / {(o.deqData.map (·.toNat)).getD 0}"

/-- A two-entry FIFO run at width 8: inputs, reference ports, design ports. -/
def fifoScenario : String := Id.run do
  let w := 8
  let ins : List (Nat × Nat × Nat) := [(1, 0, 11), (1, 0, 22), (1, 0, 33), (0, 1, 0), (1, 1, 44), (0, 1, 0), (0, 1, 0), (0, 1, 0)]
  let mut st : Store := default
  st := (Fifo.Word.design w).step st (#[0, 0, 0], true)
  let mut q := (Fifo.Word.queueSpec 2 w).init
  let mut out := "#### Scenario: width 8, after one reset cycle\n\nPorts are ready / valid / data (data shown only when valid).\n\n" ++
    "| cycle | enqValid | deqReady | data | reference | design |\n|---|---|---|---|---|---|\n"
  let mut t := 1
  for (v, r, d) in ins do
    let x := #[v, r, d]
    out := out ++ s!"| {t} | {v} | {r} | {d} | {outputText ((Fifo.Word.queueSpec 2 w).out q)} | " ++
      s!"{outputText (Fifo.Word.observe w ((Fifo.Word.design w).output st x))} |\n"
    q := (Fifo.Word.queueSpec 2 w).next q x
    st := (Fifo.Word.design w).step st (x, false)
    t := t + 1
  return out ++ "\n"

def extra (n : Name) : String :=
  if n == `HDLean.Toy16.Challenge.correctness then
    "### Interface\n\n" ++ designTables Toy16.Word.design ++ toy16Scenario
  else if n == `HDLean.RAM.Challenge.correctness then
    "### Interface (instantiated with a = 4, w = 8)\n\n" ++ designTables (RAM.Word.design 4 8) ++ ramScenario
  else if n == `HDLean.Counter.Challenge.correctness then
    "### Interface\n\n" ++ designTables Counter.Word.design ++ counterScenario
  else if n == `HDLean.Fifo.Challenge.correctness then
    "### Interface (instantiated with w = 8)\n\n" ++ designTables (Fifo.Word.design 8) ++ fifoScenario
  else if n == `HDLean.CircularFifo.Challenge.correctness then
    "### Interface (instantiated with k = 4, w = 8)\n\n" ++ designTables (Fifo.Circular.Word.design 4 8)
  else if n == `HDLean.SkidBuffer.Challenge.correctness then
    "### Interface (instantiated with w = 8)\n\n" ++ designTables (SkidBuffer.Word.design 8)
  else if n == `HDLean.AsyncFifo.Challenge.correctness then
    "### Interface (instantiated with k = 4, w = 8)\n\nDomain 0 (write) is module 0, domain 1 (read) is module 1. " ++
    "Crossing 0 carries write-domain output 1 into the read domain, crossing 1 carries read-domain output 2 " ++
    "into the write domain; the shared memory `ram` (16 × 8) is written by write-domain outputs 2–4 and read " ++
    "at read-domain output 3.\n\n" ++ designTables (AsyncFifo.Word.design 4 8).design
  else ""

/-- The review document. -/
def render (env : Environment) : IO String := do
  let mut out := "# HDLean challenge review\n\n" ++
    "Generated by `hdlean review`. Each section states what is proved, in Lean's own words, " ++
    "the axioms the proof uses (only `propext`, `Classical.choice` and `Quot.sound` are allowed), " ++
    "and, for word-level designs, the interface and scenarios computed by running both the " ++
    "specification and the design. Reading this document is enough to accept or reject a " ++
    "challenge; the proofs are checked by Lean's kernel.\n\n"
  for (n, title) in challenges do
    let (sig, doc, axs) ← describe env n
    out := out ++ s!"## {title}\n\n"
    if let some d := doc then out := out ++ d.trimAscii.toString ++ "\n\n"
    out := out ++ "```lean\n" ++ sig ++ "\n```\n\n"
    let axText := String.intercalate ", " (axs.toList.map toString)
    out := out ++ s!"Axioms: {axText}.\n\n"
    let voc ← vocabulary env n
    if !voc.isEmpty then out := out ++ "### Definitions the statement uses\n\n" ++ voc ++ "\n"
    out := out ++ extra n
  return out

end HDLean.Review
