import HDLean.MultiClock.Backend
open HDLean
namespace HDLean.Tests.MultiClock

def toggles : HDLean.MultiClock.Circuit 2 0 2 2 :=
  ⟨{ name := "dual_toggle"
     state := #v[⟨"left", .synchronous false, .inv (.reg 0), ""⟩,
                  ⟨"right", .synchronous false, .inv (.reg 1), ""⟩]
     output := #v[.reg 0, .reg 1] }, fun k => k⟩
def graph : HDLean.MultiClock.Graph := HDLean.MultiClock.compile toggles

theorem graph_correct : graph.Equivalent toggles := by
  refine ⟨?_, rfl, rfl⟩
  apply Backend.Graph.validate_sound
  decide +kernel

theorem independent_edges :
    toggles.next (fun _ => false) (Fin.elim0, false) (fun d => d.val == 0) 0 = true ∧
    toggles.next (fun _ => false) (Fin.elim0, false) (fun d => d.val == 0) 1 = false := by
  decide +kernel

end HDLean.Tests.MultiClock

def main : IO Unit := do
  let g := HDLean.Tests.MultiClock.graph
  for f in [HDLean.MultiClock.Format.systemVerilog, .rtlil] do
    let text := f.print g
    unless f.validates text g do throw (IO.userError s!"multi-clock parser roundtrip failed: {repr f}")
  let sv := HDLean.MultiClock.systemVerilog g
  let il := HDLean.MultiClock.rtlil g
  for bad in [sv.replace "posedge clk_0" "posedge clk_1", sv.replace "posedge clk_1" "negedge clk_1",
      sv.replace "input wire clk_1," "input wire clk_0,"] do
    if HDLean.MultiClock.Format.systemVerilog.validates bad g then throw (IO.userError "accepted wrong SV clock")
  for bad in [il.replace "connect \\CLK \\clk_0" "connect \\CLK \\clk_1",
      il.replace "parameter \\CLK_POLARITY 1" "parameter \\CLK_POLARITY 0"] do
    if HDLean.MultiClock.Format.rtlil.validates bad g then throw (IO.userError "accepted wrong RTLIL clock")
  IO.FS.createDirAll "build/multi-clock"
  IO.FS.writeFile "build/multi-clock/toggles.sv" sv
  IO.FS.writeFile "build/multi-clock/toggles.rtlil" il
  IO.FS.writeFile "build/multi-clock/toggles.aiger" (HDLean.Backend.aiger
    (HDLean.Backend.compile (lower HDLean.Tests.MultiClock.toggles.eventCircuit)))
  IO.println "PASS: independent clock domains, strict SV/RTLIL clocks, explicit event AIGER"
