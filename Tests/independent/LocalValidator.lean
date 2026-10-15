import HDLean.Backend.LocalValidate
import Designs.Counter.Impl
import Designs.Fifo.Impl
import Designs.Toy16.Hardware

open HDLean HDLean.Backend
namespace HDLean.Tests.LocalValidator

def tiny : Circuit 0 1 1 1 :=
  { name := "tiny"
    state := #v[⟨"q", .unreset, .inv (.reg 0), ""⟩]
    output := #v[.input 0] }
def tinyGraph : Graph := ⟨"tiny", 2, 1, #[], #[7], #[2], #["x","rst"], #["q"], #["y"], #[""]⟩

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem tiny_correct : tinyGraph.Equivalent tiny := by
  apply Graph.validateLocal_sound (hint := Local.pointerHint)
  decide +kernel

def counterCandidate : Graph := ⟨"candidate", 2, 4, #[⟨7, 9, 6⟩, ⟨8, 14, 11⟩, ⟨9, 16, 12⟩, ⟨10, 19, 7⟩, ⟨11, 20, 2⟩, ⟨12, 6, 3⟩, ⟨13, 25, 23⟩, ⟨14, 27, 5⟩, ⟨15, 8, 6⟩, ⟨16, 9, 7⟩, ⟨17, 33, 31⟩, ⟨18, 34, 19⟩, ⟨19, 36, 2⟩, ⟨20, 8, 3⟩, ⟨21, 41, 39⟩, ⟨22, 43, 5⟩, ⟨23, 30, 10⟩, ⟨24, 31, 11⟩, ⟨25, 49, 47⟩, ⟨26, 50, 19⟩, ⟨27, 52, 2⟩, ⟨28, 10, 3⟩, ⟨29, 57, 55⟩, ⟨30, 59, 5⟩, ⟨31, 46, 12⟩, ⟨32, 47, 13⟩, ⟨33, 65, 63⟩, ⟨34, 66, 19⟩, ⟨35, 68, 2⟩, ⟨36, 12, 3⟩, ⟨37, 73, 71⟩, ⟨38, 75, 5⟩], #[28, 44, 60, 76], #[6, 8, 10, 12], Array.replicate 2 "", Array.replicate 4 "", Array.replicate 4 "", Array.replicate 4 ""⟩

theorem counter_correct : counterCandidate.Equivalent Counter.hardware := by
  apply Graph.validateLocal_sound (hint := Local.pointerHint)
  decide +kernel

end HDLean.Tests.LocalValidator

private def require (b : Bool) (s : String) : IO Unit :=
  unless b do throw (IO.userError s)

def main : IO Unit := do
  let c := Counter.hardware
  let g := compileCandidate c
  require (g.validateLocal c) "counter local validation"
  require (g.validateLocal c (fun _ => 0)) "constant hints must remain correct"
  require (g.validateLocal c Local.fingerprint) "transparent hints must remain correct"
  require (!({ g with next := g.next.set! 0 (invert g.next[0]!) }).validateLocal c) "changed next accepted"
  require (!({ g with outputs := g.outputs.set! 0 (invert g.outputs[0]!) }).validateLocal c) "changed output accepted"
  let first := g.gates[0]?.getD ⟨0,0,0⟩
  require (!({ g with gates := g.gates.set! 0 { first with a := 2*first.lhs } }).validateLocal c) "cycle accepted"
  require (!({ g with gates := g.gates.set! 0 { first with lhs := first.lhs+1 } }).validateLocal c) "bad gate index accepted"
  require (!({ g with gates := g.gates.set! 0 { first with a := invert first.a } }).validateLocal c) "wrong gate accepted"
  for w in [0,1,8,16,64] do
    let c := Fifo.hardware w
    require ((compileCandidate c).validateLocal c) s!"FIFO {w} local validation"
  let cpu := Toy16.Physical.hardware (fun a => BitVec.ofNat 16 (a.toNat*257))
  require ((compileCandidate cpu).validateLocal cpu) "full CPU local validation"
  IO.println "PASS: local gate validation, all hints, mutations, FIFO widths and full CPU"
