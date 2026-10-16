import HDLean.Semantics.DeriveSynth

namespace HDLean.Tests

inductive Control where
  | idle | reading | writing
  deriving DecidableEq, Synth

structure Packet (w : Nat) where
  valid : Bool
  payload : BitVec w
  kind : Control
  deriving DecidableEq, Synth

structure Box (α : Type) where
  value : α
  valid : Bool
  deriving Synth

example : Synth.width Control = 2 := rfl
example : Synth.width (Packet 8) = 11 := rfl
example : Synth.width (Fin 1) = 0 := rfl
example : Synth.width (Fin 10) = 4 := rfl
example : Synth.width (Box (BitVec 8)) = 9 := rfl

theorem packet_roundtrip (p : Packet w) : Synth.decode (Synth.encode p) = p :=
  Synth.decode_encode p

example : Synth.decode (Synth.encode Control.writing) = Control.writing := by decide +kernel

end HDLean.Tests
