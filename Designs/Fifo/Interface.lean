import Designs.Fifo.Spec
import HDLean.Core.Circuit
namespace HDLean.Fifo

def decodeInput (xs : Fin (w + 2) → Bool) : Input (Vector Bool w) :=
  ⟨xs ⟨0, by omega⟩, Vector.ofFn (fun k => xs ⟨k.val + 2, by omega⟩), xs ⟨1, by omega⟩⟩

def observe (xs : Fin (w + 2) → Bool) : Output (Vector Bool w) :=
  ⟨xs ⟨0, by omega⟩, xs ⟨1, by omega⟩,
   if xs ⟨1, by omega⟩ then some (Vector.ofFn fun k => xs ⟨k.val + 2, by omega⟩) else none⟩

/-- Physical input decoding is the only adapter around the mathematical queue spec. -/
def wireSpec (w : Nat) : Machine (List (Vector Bool w)) (Fin (w + 2) → Bool) (Output (Vector Bool w)) where
  init := []
  out := (spec (Vector Bool w) 2).out
  next q xs := (spec (Vector Bool w) 2).next q (decodeInput xs)


end HDLean.Fifo
