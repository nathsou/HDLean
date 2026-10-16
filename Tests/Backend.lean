import HDLean
import Designs.Counter.Impl
import Designs.Fifo.Impl

namespace HDLean.Tests
open Backend Backend.Proved

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- What the CLI does at every emission: decode the emitted text with the proved
parser and compare its graph with the lowering. Also check that changed and
invalid text is rejected or decodes to a different graph. -/
def checkBackendTexts : IO Unit := do
  for width in [0, 1, 8, 16, 64] do
    let c := (Fifo.hardware width).toDag
    for f in [Format.systemVerilog, .aiger, .rtlil] do
      match f.parse (f.emit c) with
      | some g => require (g.graph.logic == c.lower.logic) s!"read-back graph differs, width={width}"
      | none => throw (IO.userError s!"proved parser rejected emitted text, width={width}")
  let c := Counter.hardware.toDag
  let sv := Format.systemVerilog.emit c
  let il := Format.rtlil.emit c
  let aag := Format.aiger.emit c
  let changes : List (Format × String × String) :=
    [(.systemVerilog, sv, sv.replace "posedge" "negedge"), (.systemVerilog, sv, sv.replace " <= " " = "),
     (.systemVerilog, sv, sv ++ "initial begin end\n"), (.systemVerilog, sv, sv.replace ";" ""),
     (.rtlil, il, il.replace "\\CLK_POLARITY 1" "\\CLK_POLARITY 0"), (.rtlil, il, il.replace "\\WIDTH 1" "\\WIDTH 2"),
     (.aiger, aag, aag.replace "aag " "aig ")]
  for (f, original, mutant) in changes do
    require (mutant != original) "mutation made no change"
    match f.parse mutant with
    | none => pure ()
    | some g => require (g.graph.logic != c.lower.logic) "a changed file decoded to the original graph"
