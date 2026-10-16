import HDLean
import Designs.Toy16.Spec

/-!
# Interface of the word-level Toy16 core (reviewer-owned)

The core is any word-level design with one 16-bit input, the instruction bus,
and the output record `CpuOut`: the fetch address and a registered retirement
report. The environment answers the fetch address shown on the outputs with
the program word at that address in the same cycle (`loop`). The challenge
reads the retirement report off the outputs (`retireAt`).
-/
namespace HDLean.Toy16.Word
open HDLean.Rtl

hdl_record CpuIn where
  instr : 16

/-- Fetch address, then the retirement report of the previous cycle. -/
hdl_record CpuOut where
  pc : 8
  valid : 1
  rpc : 8
  rinstr : 16
  rnext : 8
  wbv : 1
  wbr : 3
  wbval : 16
  stv : 1
  sta : 8
  stval : 16
  halt : 1

/-- The output record of a design in a given store (outputs do not depend on the inputs). -/
def outputsOf (d : Design) (st : Store) : CpuOut BitVec := Bundle.decode CpuOut ((d.output st #[]).getD · 0)

/-- What the outputs report: nothing, or a retired instruction. -/
def observe (o : CpuOut BitVec) : Option Retire :=
  if o.valid.getLsbD 0 then
    some { pc := o.rpc, instr := o.rinstr, nextPc := o.rnext,
           wb := if o.wbv.getLsbD 0 then some (o.wbr, o.wbval) else none,
           store := if o.stv.getLsbD 0 then some (o.sta, o.stval) else none,
           halt := o.halt.getLsbD 0 }
  else none

/-- The instruction bus: the program word at the fetch address shown on the outputs. -/
def fetchOut (d : Design) (imem : Addr → Word) (st : Store) : Array Nat := #[(imem (outputsOf d st).pc).toNat]

/-- The closed loop: the design, its instruction bus answered by `imem`, and the reset input. -/
def loop (d : Design) (imem : Addr → Word) : PMachine Store Bool Store := ⟨id, fun st r => d.step st (fetchOut d imem st, r)⟩

/-- The retirement report on the outputs at time `t`. -/
def retireAt (d : Design) (imem : Addr → Word) (s₀ : Store) (rst : Nat → Bool) (t : Nat) : Option Retire :=
  observe (outputsOf d ((loop d imem).stateFrom s₀ rst t))

end HDLean.Toy16.Word
