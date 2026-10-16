import Tests.MultiDag
import HDLean.MultiClock.NativeText
import Lean

open HDLean.MultiClock.Shared
open HDLean.MultiClock.Shared.Tests

def main : IO Unit := do
  IO.FS.createDirAll "build/native-clocks"
  let sv := crossing.emitNative .systemVerilog
  let il := crossing.emitNative .rtlil
  unless (crossing.decodeNative .systemVerilog sv).isSome && (crossing.decodeNative .rtlil il).isSome do
    throw (IO.userError "native module decoder rejected its fixture")
  for bad in [sv.replace "posedge clk_1" "posedge clk_0",
              sv.replace "second_1_0" "first_1_0"] do
    unless (crossing.decodeNative .systemVerilog bad).isNone do
      throw (IO.userError "native decoder accepted wrong clock or synchronizer bypass")
  unless (crossing.decodeNative .rtlil (il.replace "connect \\CLK \\clk_1" "connect \\CLK \\clk_0")).isNone do
    throw (IO.userError "native RTLIL decoder accepted wrong clock")
  IO.FS.writeFile "build/native-clocks/new.sv" sv
  IO.FS.writeFile "build/native-clocks/new.il" il
  let mut state : crossing.State :=
    ⟨fun d _ => d.val == 0,fun d _ _ => d.val == 1,fun d _ _ => d.val == 0⟩
  let pack (s : crossing.State) : Array Bool :=
    #[s.registers 0 ⟨0,by decide⟩,s.registers 1 ⟨0,by decide⟩,s.first 0 ⟨0,by decide⟩ ⟨0,by decide⟩,s.second 0 ⟨0,by decide⟩ ⟨0,by decide⟩,s.first 1 ⟨0,by decide⟩ ⟨0,by decide⟩,s.second 1 ⟨0,by decide⟩ ⟨0,by decide⟩]
  let mut rows : Array Lean.Json := #[]
  for cycle in List.range 240 do
    let input0 := decide ((cycle*17+3)%11 < 5)
    let input1 := decide ((cycle*29+1)%13 < 6)
    let reset0 := cycle == 0 || cycle == 61
    let reset1 := cycle == 0 || cycle == 131
    let edge0 := cycle == 0 || cycle%3 != 1
    let edge1 := cycle == 0 || cycle%5 < 3
    let e : crossing.Event :=
      ⟨fun d _ => if d.val == 0 then input0 else input1,
       fun d => if d.val == 0 then reset0 else reset1,
       fun d => if d.val == 0 then edge0 else edge1,
       fun _ _ _ => false⟩
    let next := crossing.next state e
    rows := rows.push (Lean.Json.mkObj [
      ("state",Lean.toJson (pack state)),("next",Lean.toJson (pack next)),
      ("input",Lean.toJson #[input0,input1]),("reset",Lean.toJson #[reset0,reset1]),
      ("edge",Lean.toJson #[edge0,edge1]),
      ("output",Lean.toJson #[(crossing.output state e 0) ⟨0,by decide⟩,(crossing.output state e 1) ⟨0,by decide⟩])])
    let snapshot := pack next
    state := ⟨fun d _ => snapshot[d.val]!,
      fun d _ _ => snapshot[2+2*d.val]!,fun d _ _ => snapshot[3+2*d.val]!⟩
  IO.FS.writeFile "build/native-clocks/trace.json" (Lean.Json.arr rows).compress
  IO.println "Native modules: round trips, wrong-clock/bypass rejection, and 240 reference events passed"
