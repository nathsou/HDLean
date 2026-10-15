import HDLean
import Designs.Counter.Impl
import Designs.Fifo.Impl

namespace HDLean.Tests
open Backend

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- Exercise the whole text grammar, plus behavior-changing and invalid-syntax mutations. -/
def checkBackendTexts : IO Unit := do
  for width in [0, 1, 8, 16, 64] do
    let c := Fifo.hardware width
    let g := compileCandidate c
    for format in [Format.systemVerilog, .aiger, .rtlil] do
      match checkedPrint format c with
      | .ok artifact => require (format.validates artifact.text g) s!"text validation {repr format} width={width}"
      | .error e => throw (IO.userError e)
  let g := compile (lower Counter.hardware)
  let sv := systemVerilog g
  for mutant in [sv.replace "posedge" "negedge", sv.replace " <= " " = ",
      sv.replace "in_0," "in_0", sv.replace "n1" "n01", sv.replace "= in_0;" "= n0;",
      sv.replace ";" "", sv ++ "initial begin end\n"] do
    require (mutant != sv) "SV mutation made no change"
    require (!Format.systemVerilog.validates mutant g) "accepted invalid/changed SV"
  let il := rtlil g
  for mutant in [il.replace "\\CLK_POLARITY 1" "\\CLK_POLARITY 0",
      il.replace "\\WIDTH 1" "\\WIDTH 2", il.replace "\\CLK \\clk" "\\CLK \\in_0",
      il.replace "\\n1" "\\n0", il.replace "\\n1" "\\n01",
      il.replace "autoidx 1" "autoidx 1\nattribute \\init 0"] do
    require (mutant != il) "RTLIL mutation made no change"
    require (!Format.rtlil.validates mutant g) "accepted invalid/changed RTLIL"
  let aa := aiger g
  let firstLatch := 2 * (g.inputs + 1)
  let initialized := aa.replace s!"{firstLatch} {g.next[0]!} {firstLatch}\n"
    s!"{firstLatch} {g.next[0]!} 0\n"
  require (!Format.aiger.validates initialized g) "accepted initialized AIGER latch"
  let empty : Graph := ⟨"empty", 1, 0, #[], #[], #[], #["rst"], #[], #[], #[]⟩
  for format in [Format.systemVerilog, .aiger, .rtlil] do
    require (format.validates (format.print empty) empty) "zero-output module text validation"
  IO.println "PASS: validated three backend text grammars through width 64; invalid clocks/drivers/initialization/syntax rejected."

end HDLean.Tests
