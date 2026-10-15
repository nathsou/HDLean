import Designs.Fifo.Impl
import HDLean.Netlist.Lower
namespace HDLean.Fifo

/-- Decode the physical payload registers; all bit patterns are legal power-up contents. -/
def decodeState (s : Fin (2 * w + 2) → Bool) : State (Vector Bool w) :=
  ⟨s ⟨0, by omega⟩, s ⟨1, by omega⟩,
   Vector.ofFn (fun k => s ⟨k.val + 2, by omega⟩),
   Vector.ofFn (fun k => s ⟨k.val + w + 2, by omega⟩)⟩

def decodeInput (xs : Fin (w + 2) → Bool) : Input (Vector Bool w) :=
  ⟨xs ⟨0, by omega⟩, Vector.ofFn (fun k => xs ⟨k.val + 2, by omega⟩), xs ⟨1, by omega⟩⟩

def observe (xs : Fin (w + 2) → Bool) : Output (Vector Bool w) :=
  ⟨xs ⟨0, by omega⟩, xs ⟨1, by omega⟩,
   if xs ⟨1, by omega⟩ then some (Vector.ofFn fun k => xs ⟨k.val + 2, by omega⟩) else none⟩

private theorem State.ext {a b : State α}
    (hv : a.valid = b.valid) (hf : a.full = b.full)
    (ha : a.first = b.first) (hb : a.second = b.second) : a = b := by
  cases a; cases b; simp_all

private theorem vector_if (p : Bool) (a b : Fin w → Bool) :
    (Vector.ofFn fun k => if p then a k else b k) =
      if p then Vector.ofFn a else Vector.ofFn b := by cases p <;> rfl

/-- Bit-level implementation and local finite-state implementation have identical transitions. -/
theorem decode_next (s : Fin (2 * w + 2) → Bool) (xs : Fin (w + 2) → Bool) (rst : Bool) :
    decodeState ((hardware w).next s (xs, rst)) =
      machine.next (decodeState s) (decodeInput xs, rst) := by
  apply State.ext
  · simp [decodeState, hardware, Circuit.next, Expr.eval, Expr.or, machine, decodeInput]
  · simp [decodeState, hardware, Circuit.next, Expr.eval, Expr.or, machine, decodeInput]
  · simp (disch := omega) [decodeState, hardware, Circuit.next, Expr.eval, Expr.or,
      machine, decodeInput, Nat.add_assoc, Nat.add_comm]
    split <;> split <;> simp_all
  · simp (disch := omega) [decodeState, hardware, Circuit.next, Expr.eval, Expr.or,
      machine, decodeInput, show ∀ (k : Fin w), k.val + w + 2 - w = k.val + 2 from by omega,
      show ∀ (k : Fin w), ¬k.val + w < w from by omega]
    split <;> simp_all

theorem decode_output (s : Fin (2 * w + 2) → Bool) (xs : Fin (w + 2) → Bool) :
    observe ((hardware w).evalOutput s xs) = machine.out (decodeState s) := by
  simp [observe, hardware, Circuit.evalOutput, Expr.eval, machine, decodeState]

/-- The registered FIFO outputs have no combinational dependency on inputs. -/
theorem hardware_moore (w : Nat) : (hardware w).IsMoore := by
  intro s a b
  funext k
  simp only [Circuit.evalOutput]
  dsimp [hardware]
  simp only [Vector.getElem_ofFn]
  split <;> (try split) <;> rfl

/-- Physical input decoding is the only adapter around the mathematical queue spec. -/
def wireSpec (w : Nat) : Machine (List (Vector Bool w)) (Fin (w + 2) → Bool) (Output (Vector Bool w)) where
  init := []
  out := (spec (Vector Bool w) 2).out
  next q xs := (spec (Vector Bool w) 2).next q (decodeInput xs)

/-- Headline theorem is about the synthesizable AST itself, for every payload width. -/
theorem hardware_correct (w : Nat) :
    RefinesAfterReset ((hardware w).denote (hardware_moore w)) (wireSpec w) observe 1 := by
  apply refinesAfterReset_of_simulation _ _ _ _ (fun s q => Relation (decodeState s) q)
  · intro s xs hr
    have h := hr 0 (by omega)
    change Relation (decodeState ((hardware w).next s (xs 0))) []
    rw [show xs 0 = ((xs 0).1, (xs 0).2) from rfl, decode_next]
    simp [machine, h, Relation]
  · intro s q xs h
    change Relation (decodeState ((hardware w).next s (xs, false))) _
    rw [decode_next]
    exact relation_step _ _ _ h
  · intro s q h
    change observe ((hardware w).evalOutput s (fun _ => false)) = _
    rw [decode_output]
    exact relation_out _ _ h

/-- Exact flip-flop budget for this shift-register implementation; no hidden resettable payload. -/
theorem hardware_ffBits (w : Nat) : (lower (hardware w)).ffBits = 2 * w + 2 := rfl

end HDLean.Fifo
