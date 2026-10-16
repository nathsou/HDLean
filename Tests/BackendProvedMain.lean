import Tests.BackendProved
import HDLean.Backend.SystemVerilogProved
import HDLean.Backend.RTLILProved
open HDLean HDLean.Backend HDLean.Backend.Proved

def main : IO Unit := do
  let g := Aag.ofGraph Dag.Tests.exampleDag.lower
  IO.FS.createDirAll "build/proved-backends"
  IO.FS.writeFile "build/proved-backends/new.sv" g.systemVerilog
  IO.FS.writeFile "build/proved-backends/new.il" g.rtlil
  IO.FS.writeFile "build/proved-backends/new.aag" g.print
  unless (Aag.parse g.print).isSome && (Aag.parseSystemVerilog g.systemVerilog).isSome &&
    (Aag.parseRTLIL g.rtlil).isSome do throw (IO.userError "roundtrip failed")
  unless (Aag.parseSystemVerilog (g.systemVerilog ++ "assign bad = 1;\n")).isNone &&
    (Aag.parseRTLIL (g.rtlil.replace "parameter \\CLK_POLARITY 1" "parameter \\CLK_POLARITY 0")).isNone &&
    (Aag.parse (g.print.replace "aag" "aig")).isNone do throw (IO.userError "malformed text accepted")
  for si in [:8] do
    for ii in [:4] do
      let state := (Array.range 3).map fun k => si.testBit k
      let inputs := (Array.range 2).map fun k => ii.testBit k
      let result := Dag.Tests.exampleDag.lower.eval inputs state
      IO.println s!"{si} {ii} {result.1.foldr (fun b n => 2*n + if b then 1 else 0) 0} {result.2.foldr (fun b n => 2*n + if b then 1 else 0) 0}"
