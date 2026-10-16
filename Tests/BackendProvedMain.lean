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
  let aliasName := g.systemVerilog.replace " & n_2 ;" " & n_02 ;"
  let target := 2*(g.inputs+g.next.length+1)
  let oddSV := g.systemVerilog.replace s!"wire n_{target} = g_0 ;" s!"wire n_{target+1} = g_0 ;"
  let oddIL := g.rtlil.replace s!"connect \\n [ {target} ] \\gates [ 0 ]" s!"connect \\n [ {target+1} ] \\gates [ 0 ]"
  unless aliasName != g.systemVerilog && oddSV != g.systemVerilog && oddIL != g.rtlil do
    throw (IO.userError "malformed identifier/target fixtures did not change the input")
  unless (Aag.parseSystemVerilog aliasName).isNone && (Aag.parseSystemVerilog oddSV).isNone &&
      (Aag.parseRTLIL oddIL).isNone do
    throw (IO.userError "noncanonical name or odd physical target was accepted")
  let noRegs : Aag := ⟨1,[],[0],[]⟩
  let badWidth := noRegs.rtlil.replace "wire width 1 \\state" "wire width 0 \\state"
  unless badWidth != noRegs.rtlil && (Aag.parseRTLIL badWidth).isNone do
    throw (IO.userError "zero-width padding was accepted")
  for si in [:8] do
    for ii in [:4] do
      let state := (Array.range 3).map fun k => si.testBit k
      let inputs := (Array.range 2).map fun k => ii.testBit k
      let result := Dag.Tests.exampleDag.lower.eval inputs state
      IO.println s!"{si} {ii} {result.1.foldr (fun b n => 2*n + if b then 1 else 0) 0} {result.2.foldr (fun b n => 2*n + if b then 1 else 0) 0}"
