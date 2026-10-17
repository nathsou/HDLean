import HDLean
import HDLean.Lib.Memory

/-!
# Interface of the word-level single-port RAM (reviewer-owned)

Inputs `we`, `addr`, `wdata`; output `rdata`. The read word is the output word
(`readWord`); the inputs of each cycle are read as a reference request
(`request`). Reset is an input like any other; the reference RAM has none.
-/
namespace HDLean.RAM.Word
open HDLean.Rtl

hdl_record In (a w : Nat) where
  we : 1
  addr : a
  wdata : w

hdl_record Out (w : Nat) where
  rdata : w

/-- The input words as a reference request. -/
def request (a w : Nat) (ins : Array Nat) : RAMRequest (2 ^ a) w :=
  let i := Bundle.decode (In a w) (ins.getD · 0)
  ⟨i.addr.toFin, if i.we.getLsbD 0 then some i.wdata else none⟩

/-- A design as a machine over stores: inputs are the port words and the reset level. -/
def machine (d : Design) : PMachine Store (Array Nat × Bool) Store := ⟨id, d.step⟩

/-- The read port, as a word of width `w`. -/
def readWord (w : Nat) (d : Design) (st : Store) : BitVec w := bv w ((d.output st #[]).getD 0 0)

end HDLean.RAM.Word
