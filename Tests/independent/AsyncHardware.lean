import Designs.AsyncFifo.Hardware
import HDLean.MultiClock.Backend
import Lean

open HDLean Lean

private def bools (a : Array Bool) : Json := toJson a

/-- Concrete external-tool fixture; expectations are the physical circuit's event
semantics, which decode_next relates to the abstract FIFO for every initial state. -/
def main (args : List String) : IO Unit := do
  let folder := args.headD "build/async-hardware"
  IO.FS.createDirAll folder
  let c := AsyncFifo.Physical.hardware 1 4
  let g := MultiClock.compile c
  unless g.wellFormed && g.logic.validate c.combinational do
    throw (IO.userError "async graph validation failed")
  let sv := MultiClock.Format.systemVerilog.print g
  let il := MultiClock.Format.rtlil.print g
  unless MultiClock.Format.systemVerilog.validates sv g && MultiClock.Format.rtlil.validates il g do
    throw (IO.userError "async physical text validation failed")
  for bad in [sv.replace "posedge clk_0" "posedge clk_1", sv.replace "posedge clk_1" "negedge clk_1"] do
    if MultiClock.Format.systemVerilog.validates bad g then throw (IO.userError "accepted wrong async SV clock")
  for bad in [il.replace "connect \\CLK \\clk_0" "connect \\CLK \\clk_1",
      il.replace "parameter \\CLK_POLARITY 1" "parameter \\CLK_POLARITY 0"] do
    if MultiClock.Format.rtlil.validates bad g then throw (IO.userError "accepted wrong async RTLIL clock")
  IO.FS.writeFile (folder ++ "/async.sv") sv
  IO.FS.writeFile (folder ++ "/async.rtlil") il
  IO.FS.writeFile (folder ++ "/async.aiger") (Backend.aiger (Backend.compile (lower c.eventCircuit)))
  let mut state : Vector Bool 32 := Vector.ofFn fun j => j.val % 3 == 0
  let mut rows : Array Json := #[]
  let mut seed := 42
  for t in [:160] do
    seed := Verification.random seed
    let xs : Vector Bool 8 := Vector.ofFn fun j =>
      if j.val < 2 then t < 4 else (seed / 2^(j.val-2)) % 2 == 1
    let edge : Vector Bool 2 := Vector.ofFn fun j => (t / 2^j.val) % 2 == 1
    let next := Vector.ofFn (c.next (fun j => state[j]) ((fun j => xs[j]), false) (fun d => edge[d]))
    let outs := Vector.ofFn (c.output (fun j => state[j]) (fun j => xs[j]))
    let actual := g.eval (fun d => edge.toArray[d]?.getD false) (xs.toArray.push false) state.toArray
    unless actual.1 == next.toArray && actual.2 == outs.toArray do
      throw (IO.userError s!"async graph event mismatch at {t}")
    rows := rows.push (Json.mkObj [("cycle", toJson t), ("inputs", bools (xs.toArray.push false)),
      ("edges", bools edge.toArray), ("state", bools state.toArray),
      ("next", bools next.toArray), ("outputs", bools outs.toArray)])
    state := next
  IO.FS.writeFile (folder ++ "/trace.json") (toJson rows).compress
  IO.FS.writeFile (folder ++ "/clocks.json") (toJson g.clock).compress
  IO.println "PASS: async graph, native clocks, parser mutations, event traces"
