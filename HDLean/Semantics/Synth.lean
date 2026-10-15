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

/-- Product encodings concatenate two independently verified layouts. -/
instance [Synth α] [Synth β] : Synth (α × β) where
  width := Synth.width α + Synth.width β
  encode x := Synth.encode x.1 ++ Synth.encode x.2
  decode x := (Synth.decode (x.extractLsb' (Synth.width β) (Synth.width α)),
    Synth.decode (x.extractLsb' 0 (Synth.width β)))
  decode_encode x := by
    simp [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right, Synth.decode_encode]

/-- Transport a layout through a proved representation map (used for structures and enums). -/
@[instance_reducible] def Synth.transport [Synth β] (encode : α → β) (decode : β → α)
    (inverse : ∀ a, decode (encode a) = a) : Synth α where
  width := Synth.width β
  encode a := Synth.encode (encode a)
  decode b := decode (Synth.decode b)
  decode_encode a := by rw [Synth.decode_encode, inverse]

/-- A conservative fixed-width encoding of nonempty finite types; unused patterns decode modulo n. -/
instance : Synth (Fin (n + 1)) where
  width := n + 1
  encode a := BitVec.ofNat (n + 1) a.val
  decode b := ⟨b.toNat % (n + 1), Nat.mod_lt _ (by omega)⟩
  decode_encode a := by
    apply Fin.ext
    have h : a.val < 2 ^ (n + 1) := Nat.lt_trans a.isLt (Nat.lt_two_pow_self)
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt a.isLt]

@[instance_reducible] private def synthVector [Synth α] : (n : Nat) → Synth (Vector α n)
  | 0 =>
    { width := 0, encode := fun _ => 0, decode := fun _ => #v[],
      decode_encode := fun a => by apply Vector.ext; intro i h; omega }
  | n + 1 =>
    letI : Synth (Vector α n) := synthVector n
    Synth.transport (β := Vector α n × α) (fun v : Vector α (n + 1) => (v.pop, v.back))
      (fun p : Vector α n × α => p.1.push p.2) (fun v => by simp)

instance [Synth α] : Synth (Vector α n) := synthVector n

end HDLean
