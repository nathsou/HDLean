import HDLean
import Designs.Counter.Spec

/-!
# Interface of the word-level decade counter (reviewer-owned)

Input 0 is `en` (one bit); output 0 is `value` (four bits). The design must be
a Moore machine (its outputs are read from the store alone); `Design.denote`
then views it as a machine over stores whose inputs are the port words and the
reset level.
-/
namespace HDLean.Counter.Word
open HDLean.Rtl

hdl_record In where
  en : 1

hdl_record Out where
  value : 4

/-- The enable bit of the input words. -/
def enable (ins : Array Nat) : Bool := (Bundle.decode In (ins.getD · 0)).en.getLsbD 0

/-- The reviewed counter, read through the input words. -/
def wordSpec : Machine Nat (Array Nat) Nat where
  init := 0
  out := id
  next n ins := spec.next n (enable ins)

/-- The output word, read at its width. -/
def value (outs : Array Nat) : Nat := (Bundle.decode Out (outs.getD · 0)).value.toNat

end HDLean.Counter.Word
