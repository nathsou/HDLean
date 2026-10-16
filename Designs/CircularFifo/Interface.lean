import Designs.Fifo.Spec
import HDLean.Core.Expr

/-!
Ports of the general-depth FIFO and the queue reference they must follow.
Reviewer-owned and frozen; independent of any implementation.
Port layout: input 0 = enqValid, 1 = deqReady, 2.. = payload (LSB first);
output 0 = enqReady, 1 = deqValid, 2.. = payload.
-/

namespace HDLean.Fifo.Circular.Reference

/-- The payload bits, LSB first, starting at port 2. -/
def payload (values : Fin (w+2) → Bool) : BitVec w :=
  (WordExpr.inputs 2 (by omega) : WordExpr 0 (w+2) 0 w).eval values Fin.elim0

def decodeInput (w : Nat) (xs : Fin (w+2) → Bool) : Input (BitVec w) :=
  ⟨xs ⟨0,by omega⟩, payload xs, xs ⟨1,by omega⟩⟩

/-- Data counts only when valid. -/
def observe (values : Fin (w+2) → Bool) : Output (BitVec w) :=
  ⟨values ⟨0,by omega⟩, values ⟨1,by omega⟩,
    if values ⟨1,by omega⟩ then some (payload values) else none⟩

/-- The reviewed bounded queue at capacity 2^k, read through the port layout. -/
def queueSpec (k w : Nat) : Machine (List (BitVec w)) (Fin (w+2) → Bool) (Output (BitVec w)) where
  init := []
  out := (Fifo.spec (BitVec w) (2^k)).out
  next q i := (Fifo.spec (BitVec w) (2^k)).next q (decodeInput w i)

end HDLean.Fifo.Circular.Reference
