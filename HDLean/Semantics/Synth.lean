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

instance : Synth Unit where
  width := 0
  encode _ := 0
  decode _ := ()
  decode_encode a := by cases a; rfl

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

/-- Minimal unsigned width for values 0..maximum; a singleton needs no wire bits. -/
def finWidth (maximum : Nat) : Nat := if maximum = 0 then 0 else maximum.log2 + 1

theorem finWidth_bound (a : Fin (n + 1)) : a.val < 2 ^ finWidth n := by
  by_cases hn : n = 0
  · subst n
    have ha : a.val = 0 := by omega
    simp [finWidth]
  · simp only [finWidth, ite_eq_right hn]
    exact Nat.lt_of_le_of_lt (by omega) Nat.lt_log2_self

/-- Compact finite-type encoding; unused bit patterns decode modulo the cardinality. -/
instance : Synth (Fin (n + 1)) where
  width := finWidth n
  encode a := BitVec.ofNat (finWidth n) a.val
  decode b := ⟨b.toNat % (n + 1), Nat.mod_lt _ (by omega)⟩
  decode_encode a := by
    apply Fin.ext
    have h := finWidth_bound a
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
