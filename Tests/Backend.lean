import HDLean
import Designs.Counter.Word
import Designs.Fifo.Word

namespace HDLean.Tests
open Backend Backend.Proved

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- What the CLI does at every emission: decode the emitted text with the proved
parser and compare its graph with the lowering. Also check that changed and
invalid text is rejected or decodes to a different graph. -/
def checkBackendTexts : IO Unit := do
  for width in [1, 8, 16, 64] do
    let some c := (Fifo.Word.design width).toDag
      | throw (IO.userError s!"the FIFO does not bit-blast, width={width}")
    for f in [Format.systemVerilog, .aiger, .rtlil] do
      match f.parse (f.emit c) with
      | some g => require (g.graph.logic == (Dag.lowerOpt c).logic) s!"read-back graph differs, width={width}"
      | none => throw (IO.userError s!"proved parser rejected emitted text, width={width}")
  let some c := Counter.Word.design.toDag
    | throw (IO.userError "the counter does not bit-blast")
  let sv := Format.systemVerilog.emit c
  let il := Format.rtlil.emit c
  let aag := Format.aiger.emit c
  let changes : List (Format × String × String) :=
    [(.systemVerilog, sv, sv.replace "posedge" "negedge"), (.systemVerilog, sv, sv.replace " <= " " = "),
     (.systemVerilog, sv, sv ++ "initial begin end\n"), (.systemVerilog, sv, sv.replace ";" ""),
     (.rtlil, il, il.replace "\\CLK_POLARITY 1" "\\CLK_POLARITY 0"), (.rtlil, il, il.replace "\\WIDTH 1" "\\WIDTH 2"),
     (.aiger, aag, aag.replace "aag " "aig ")]
  -- An external graph without a valid certificate is never adopted, whether it
  -- is correct (ABC-like: the optimised graph itself) or wrong (an inverted output).
  let g := Dag.lowerOpt c
  let wrong : Graph := { g with outputs := g.outputs.modify 0 (· ^^^ 1) }
  require ((Validate.select g wrong #[]).logic == g.logic) "a wrong graph was adopted without a certificate"
  require ((Validate.select g g #[]).logic == g.logic) "select changed the graph"
  require (Validate.miter g wrong).isSome "the miter of graphs with equal ports was not built"
  for (f, original, mutant) in changes do
    require (mutant != original) "mutation made no change"
    match f.parse mutant with
    | none => pure ()
    | some g => require (g.graph.logic != (Dag.lowerOpt c).logic) "a changed file decoded to the original graph"

/-- The word-level pass on a module written with redundancy: constants, identities,
a constant-select mux and duplicate cells are rewritten, the result still passes
`Design.check`, and it computes the same outputs and next state. -/
def checkWordPass : IO Unit := do
  let c (w : Nat) (op : Rtl.Op) : Rtl.Cell := ⟨w, op⟩
  let m : Rtl.Module :=
    { name := .ofString "redundant", inputs := #[⟨.ofString "x", 8⟩, ⟨.ofString "y", 8⟩]
      outputs := #[⟨.ofString "o", 13⟩, ⟨.ofString "p", 14⟩]
      cells := #[c 8 (.input 0), c 8 (.input 1), c 8 (.const 0), c 1 (.const 1), c 8 (.const 3),
        c 8 (.bin .add 0 2),        -- x + 0           → x
        c 8 (.bin .and 0 0),        -- x & x           → x
        c 8 (.bin .add 0 1),        -- x + y
        c 8 (.bin .add 0 1),        -- duplicate       → wire to 7
        c 8 (.mux 3 7 1),           -- select 1        → 7
        c 8 (.bin .mul 4 4),        -- 3 * 3           → 9
        c 8 (.bin .xor 1 1),        -- y ^ y           → 0
        c 1 (.cmp .eq 8 0 0),       -- x == x          → 1
        c 8 (.bin .sub 8 11),       -- (x+y) - 0       → x + y
        c 8 (.bin .or 13 10)]
      regs := #[⟨.ofString "r", 8, .sync 0, 14⟩], mems := #[] }
  let d : Rtl.Design := ⟨#[m]⟩
  require d.check "the redundant test module does not pass Design.check"
  let o := d.optimize
  require o.check "the optimised module does not pass Design.check"
  let changed := ((m.cells.zip o.modules[0]!.cells).toList.filter fun (a, b) => a != b).length
  require (changed ≥ 8) s!"the word-level pass rewrote only {changed} cells"
  let c := d.optimized
  require (c.modules[0]!.cells.size < m.cells.size) "dead-cell removal kept every cell"
  require c.check "the compacted module does not pass Design.check"
  for x in [0, 1, 7, 200, 255] do
    for y in [0, 3, 128, 255] do
      let st : Rtl.Store := .mk #[x ^^^ y] #[] #[]
      require (o.output st #[x, y] == d.output st #[x, y]) "the optimised outputs differ"
      require (c.output st #[x, y] == d.output st #[x, y]) "the compacted outputs differ"
      require ((c.step st (#[x, y], false)).regs == (d.step st (#[x, y], false)).regs) "the compacted state differs"
      require ((o.step st (#[x, y], false)).regs == (d.step st (#[x, y], false)).regs) "the optimised state differs"
