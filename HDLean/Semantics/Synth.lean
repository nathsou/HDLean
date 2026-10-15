import Std
namespace HDLean

/-- Only finite, fixed-width encodings can cross a hardware interface. -/
class Synth (α : Type) where
  width : Nat
  encode : α → BitVec width
  decode : BitVec width → α
  decode_encode : ∀ a, decode (encode a) = a

instance : Synth (BitVec n) := ⟨n, id, id, fun _ => rfl⟩
instance : Synth Bool where
  width := 1
  encode b := if b then 1 else 0
  decode v := v != 0
  decode_encode b := by cases b <;> decide

/-- An encoding is injective: two distinct hardware values never share a bit pattern. -/
theorem Synth.encode_injective [Synth α] : Function.Injective (Synth.encode (α := α)) := by
  intro a b h
  have := congrArg Synth.decode h
  simpa only [Synth.decode_encode] using this

end HDLean
