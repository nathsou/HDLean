import Designs.AsyncFifo.Proof
import HDLean.MultiClock.Core
import HDLean.MultiClock.Word
import HDLean.Lib.MemoryCircuit

set_option linter.unusedSimpArgs false
namespace HDLean.AsyncFifo.Physical
open WordExpr

/-- A uniform bank keeps finite indexing simple. Pointer/data padding is ordinary
unreset storage and is accounted for in the exact physical register count. -/
def bankWidth (k w : Nat) := max (k+1) w
def entries (k : Nat) := 6 + 2^k
abbrev E (k w : Nat) := Expr 0 (4+w) (entries k * bankWidth k w)
abbrev W (k w n : Nat) := WordExpr 0 (4+w) (entries k * bankWidth k w) n

def word (k w : Nat) (j : Fin (entries k)) : W k w (bankWidth k w) := bankWord j
def pointer (k w : Nat) (j : Fin 6) : W k w (k+1) :=
  setWidth (word k w ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right 6 (2^k))⟩) (k+1)
def cell (k w : Nat) (j : Fin (2^k)) : W k w w :=
  setWidth (word k w ⟨6+j.val, by unfold entries; omega⟩) w

def payload (k w : Nat) : W k w w := inputs 4 (by omega)
def writeReset (k w : Nat) : E k w := .input ⟨0, by omega⟩
def readReset (k w : Nat) : E k w := .input ⟨1, by omega⟩
def ready (k w : Nat) : E k w := .inv (equal (pointer k w 0)
  (bitXor (WordExpr.ungray (pointer k w 5)) (literal (BitVec.ofNat (k+1) (2^k)))))
def valid (k w : Nat) : E k w := .inv (equal (pointer k w 1) (WordExpr.ungray (pointer k w 3)))
def push (k w : Nat) : E k w := .and (.and (.inv (writeReset k w)) (.input ⟨2, by omega⟩)) (ready k w)
def pop (k w : Nat) : E k w := .and (.and (.inv (readReset k w)) (.input ⟨3, by omega⟩)) (valid k w)

def clock (k : Nat) (j : Fin (entries k)) : Fin 2 :=
  if j.val = 1 ∨ j.val = 2 ∨ j.val = 3 then 1 else 0

def writeCrossing (k w : Nat) : W k w (k+1) × W k w (k+1) :=
  MultiClock.sync2Words (source := (0 : Fin 2)) (target := (1 : Fin 2))
    ⟨readReset k w⟩ ⟨WordExpr.gray (pointer k w 0)⟩ ⟨pointer k w 2⟩
def readCrossing (k w : Nat) : W k w (k+1) × W k w (k+1) :=
  MultiClock.sync2Words (source := (1 : Fin 2)) (target := (0 : Fin 2))
    ⟨writeReset k w⟩ ⟨WordExpr.gray (pointer k w 1)⟩ ⟨pointer k w 4⟩

/-- Both named two-flop crossings terminate in the other domain. The native
single-event semantics samples old source values; the safety theorem additionally
covers the full arbitrary-mask metastability abstraction. -/
def nextWord (k w : Nat) (j : Fin (entries k)) : W k w (bankWidth k w) :=
  let pointerNext (rst : E k w) (value : W k w (k+1)) :=
    setWidth (mux rst (literal 0) value) (bankWidth k w)
  if j.val = 0 then pointerNext (writeReset k w)
    (mux (push k w) (add (pointer k w 0) (literal 1)) (pointer k w 0))
  else if j.val = 1 then pointerNext (readReset k w)
    (mux (pop k w) (add (pointer k w 1) (literal 1)) (pointer k w 1))
  else if j.val = 2 then setWidth (writeCrossing k w).1 (bankWidth k w)
  else if j.val = 3 then setWidth (writeCrossing k w).2 (bankWidth k w)
  else if j.val = 4 then setWidth (readCrossing k w).1 (bankWidth k w)
  else if j.val = 5 then setWidth (readCrossing k w).2 (bankWidth k w)
  else mux (.and (push k w)
    (equal (setWidth (pointer k w 0) k) (literal (BitVec.ofNat k (j.val-6)))))
    (setWidth (payload k w) (bankWidth k w)) (word k w j)

def output (k w : Nat) : Vector (E k w) (2+w) :=
  #v[ready k w, valid k w] ++ select (setWidth (pointer k w 1) k) (cell k w)

def hardware (k w : Nat) : MultiClock.Circuit 2 (4+w) (entries k * bankWidth k w) (2+w) :=
  MultiClock.wordBank s!"async_fifo_{2^k}x{w}" (clock k) (fun _ => .unreset) (nextWord k w) (output k w)

def decode (k w : Nat) (s : Fin (entries k * bankWidth k w) → Bool) : State k w :=
  { memory := fun a => (cell k w a.toFin).eval (fun _ => false) s
    write := (pointer k w 0).eval (fun _ => false) s
    read := (pointer k w 1).eval (fun _ => false) s
    seenWrite := ⟨(pointer k w 2).eval (fun _ => false) s, (pointer k w 3).eval (fun _ => false) s⟩
    seenRead := ⟨(pointer k w 4).eval (fun _ => false) s, (pointer k w 5).eval (fun _ => false) s⟩ }

def decodeInput (k w : Nat) (xs : Fin (4+w) → Bool) (edge : Fin 2 → Bool) : Input k w :=
  ⟨edge 0, edge 1, xs ⟨0, by omega⟩, xs ⟨1, by omega⟩,
    xs ⟨2, by omega⟩, (payload k w).eval xs (fun _ => false), xs ⟨3, by omega⟩, -1, -1⟩

@[simp] theorem word_inputs (j : Fin (entries k)) (s) (xs ys : Fin (4+w) → Bool) :
    (word k w j).eval xs s = (word k w j).eval ys s := bankWord_inputs j s xs ys
@[simp] theorem pointer_inputs (j : Fin 6) (s) (xs ys : Fin (4+w) → Bool) :
    (pointer k w j).eval xs s = (pointer k w j).eval ys s := by
  simp only [pointer, setWidth_correct]
  rw [word_inputs _ s xs ys]
@[simp] theorem cell_inputs (j : Fin (2^k)) (s) (xs ys : Fin (4+w) → Bool) :
    (cell k w j).eval xs s = (cell k w j).eval ys s := by
  simp only [cell, setWidth_correct]
  rw [word_inputs _ s xs ys]
@[simp] theorem payload_state (xs) (s t : Fin (entries k * bankWidth k w) → Bool) :
    (payload k w).eval xs s = (payload k w).eval xs t := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [eval_bit _ _ _ j hj, eval_bit _ _ _ j hj]
  simp [payload, inputs, Expr.eval]

theorem word_next (k w : Nat) (j : Fin (entries k)) (s xs rst edge) :
    (word k w j).eval xs ((hardware k w).next s (xs,rst) edge) =
      if edge (clock k j) then (nextWord k w j).eval xs s else (word k w j).eval xs s := by
  change (bankWord j).eval xs ((MultiClock.wordBank _ _ _ _ _).next s (xs,rst) edge) = _
  exact MultiClock.wordBank_next s!"async_fifo_{2^k}x{w}"
    (clock k) (fun _ => .unreset) (nextWord k w) (output k w) s xs rst edge j

theorem ready_correct (k w : Nat) (xs s) :
    (ready k w).eval xs s = AsyncFifo.enqReady (decode k w s) := by
  simp only [ready, Expr.eval, equal_correct, bitXor_correct, ungray_correct, eval_literal]
  rw [pointer_inputs 0 s xs (fun _ => false), pointer_inputs 5 s xs (fun _ => false)]
  rfl

theorem valid_correct (k w : Nat) (xs s) :
    (valid k w).eval xs s = AsyncFifo.deqValid (decode k w s) := by
  simp only [valid, Expr.eval, equal_correct, ungray_correct]
  rw [pointer_inputs 1 s xs (fun _ => false), pointer_inputs 3 s xs (fun _ => false)]
  rfl

theorem push_correct (k w : Nat) (xs s edge) :
    (edge 0 && (push k w).eval xs s) = AsyncFifo.push (decode k w s) (decodeInput k w xs edge) := by
  simp [push, Expr.eval, writeReset, ready_correct, AsyncFifo.push, decodeInput, Bool.and_assoc]
theorem pop_correct (k w : Nat) (xs s edge) :
    (edge 1 && (pop k w).eval xs s) = AsyncFifo.pop (decode k w s) (decodeInput k w xs edge) := by
  simp [pop, Expr.eval, readReset, valid_correct, AsyncFifo.pop, decodeInput, Bool.and_assoc]

private theorem pointer_next (k w : Nat) (j : Fin 6) (s xs rst edge) :
    (pointer k w j).eval (fun _ => false) ((hardware k w).next s (xs,rst) edge) =
      if edge (clock k ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right 6 (2^k))⟩) then
        ((nextWord k w ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right 6 (2^k))⟩).eval xs s).setWidth (k+1)
      else (pointer k w j).eval (fun _ => false) s := by
  rw [pointer_inputs j _ (fun _ => false) xs]
  simp only [pointer, setWidth_correct]
  rw [word_next]
  split
  · rfl
  · rw [word_inputs _ s xs (fun _ => false)]

theorem pointer_write_next (k w : Nat) (s xs rst edge) :
    (decode k w ((hardware k w).next s (xs,rst) edge)).write =
    (AsyncFifo.next (decode k w s) (decodeInput k w xs edge)).write := by
  change (pointer k w 0).eval (fun _ => false) _ = _
  rw [pointer_next]
  simp only [clock, nextWord, Fin.val_zero, ↓reduceIte, show ¬(0 = 1 ∨ 0 = 2 ∨ 0 = 3) by decide,
    setWidth_correct, eval_mux, eval_literal, add_correct, writeReset, Expr.eval]
  have hw : k+1 ≤ bankWidth k w := Nat.le_max_left _ _
  simp only [BitVec.setWidth_setWidth_of_le _ hw, BitVec.setWidth_eq]
  rw [pointer_inputs 0 s xs (fun _ => false)]
  simp only [AsyncFifo.next, ← push_correct k w xs s edge]
  simp only [decodeInput, decode]
  by_cases he : edge 0 = true <;> by_cases hr : xs ⟨0, by omega⟩ = true <;> simp [he, hr]

theorem pointer_read_next (k w : Nat) (s xs rst edge) :
    (decode k w ((hardware k w).next s (xs,rst) edge)).read =
    (AsyncFifo.next (decode k w s) (decodeInput k w xs edge)).read := by
  change (pointer k w 1).eval (fun _ => false) _ = _
  rw [pointer_next]
  simp [clock, nextWord, readReset, Expr.eval]
  have hw : k+1 ≤ bankWidth k w := Nat.le_max_left _ _
  simp only [BitVec.setWidth_setWidth_of_le _ hw, BitVec.setWidth_eq]
  rw [pointer_inputs 1 s xs (fun _ => false)]
  simp only [AsyncFifo.next, ← pop_correct k w xs s edge]
  simp only [decodeInput, decode]
  by_cases he : edge 1 = true <;> by_cases hr : xs ⟨1, by omega⟩ = true <;> simp [he, hr]

theorem sync_write_first_next (k w : Nat) (s xs rst edge) :
    (decode k w ((hardware k w).next s (xs,rst) edge)).seenWrite.first =
    (AsyncFifo.next (decode k w s) (decodeInput k w xs edge)).seenWrite.first := by
  change (pointer k w 2).eval (fun _ => false) _ = _
  rw [pointer_next]
  have hw : k+1 ≤ bankWidth k w := Nat.le_max_left _ _
  simp only [clock, nextWord, writeCrossing, readCrossing, MultiClock.sync2Words]
  simp only [show ((2 : Fin 6).val) = 2 from rfl]
  simp only [Nat.reduceEqDiff, Nat.reduceEqDiff, Bool.false_eq_true]
  simp [writeReset, readReset, Expr.eval, BitVec.setWidth_setWidth_of_le _ hw,
    pointer_inputs 0 s xs (fun _ => false), AsyncFifo.next, decodeInput, decode,
    sampleBits, BitVec.neg_one_eq_allOnes]
  by_cases he : edge 1 = true <;> by_cases hr : xs ⟨1, by omega⟩ = true <;> simp [he, hr]

theorem sync_write_second_next (k w : Nat) (s xs rst edge) :
    (decode k w ((hardware k w).next s (xs,rst) edge)).seenWrite.second =
    (AsyncFifo.next (decode k w s) (decodeInput k w xs edge)).seenWrite.second := by
  change (pointer k w 3).eval (fun _ => false) _ = _
  rw [pointer_next]
  have hw : k+1 ≤ bankWidth k w := Nat.le_max_left _ _
  simp only [clock, nextWord, writeCrossing, readCrossing, MultiClock.sync2Words]
  simp only [show ((3 : Fin 6).val) = 3 from rfl]
  simp only [Nat.reduceEqDiff, Nat.reduceEqDiff, Bool.false_eq_true]
  simp [writeReset, readReset, Expr.eval, BitVec.setWidth_setWidth_of_le _ hw,
    pointer_inputs 2 s xs (fun _ => false), AsyncFifo.next, decodeInput, decode,
    sampleBits, BitVec.neg_one_eq_allOnes]
  by_cases he : edge 1 = true <;> by_cases hr : xs ⟨1, by omega⟩ = true <;> simp [he, hr]

theorem sync_read_first_next (k w : Nat) (s xs rst edge) :
    (decode k w ((hardware k w).next s (xs,rst) edge)).seenRead.first =
    (AsyncFifo.next (decode k w s) (decodeInput k w xs edge)).seenRead.first := by
  change (pointer k w 4).eval (fun _ => false) _ = _
  rw [pointer_next]
  have hw : k+1 ≤ bankWidth k w := Nat.le_max_left _ _
  simp only [clock, nextWord, writeCrossing, readCrossing, MultiClock.sync2Words]
  simp only [show ((4 : Fin 6).val) = 4 from rfl]
  simp only [Nat.reduceEqDiff, Nat.reduceEqDiff, Bool.false_eq_true]
  simp [writeReset, readReset, Expr.eval, BitVec.setWidth_setWidth_of_le _ hw,
    pointer_inputs 1 s xs (fun _ => false), AsyncFifo.next, decodeInput, decode,
    sampleBits, BitVec.neg_one_eq_allOnes]
  by_cases he : edge 0 = true <;> by_cases hr : xs ⟨0, by omega⟩ = true <;> simp [he, hr]

theorem sync_read_second_next (k w : Nat) (s xs rst edge) :
    (decode k w ((hardware k w).next s (xs,rst) edge)).seenRead.second =
    (AsyncFifo.next (decode k w s) (decodeInput k w xs edge)).seenRead.second := by
  change (pointer k w 5).eval (fun _ => false) _ = _
  rw [pointer_next]
  have hw : k+1 ≤ bankWidth k w := Nat.le_max_left _ _
  simp only [clock, nextWord, writeCrossing, readCrossing, MultiClock.sync2Words]
  simp only [show ((5 : Fin 6).val) = 5 from rfl]
  simp only [Nat.reduceEqDiff, Nat.reduceEqDiff, Bool.false_eq_true]
  simp [writeReset, readReset, Expr.eval, BitVec.setWidth_setWidth_of_le _ hw,
    pointer_inputs 4 s xs (fun _ => false), AsyncFifo.next, decodeInput, decode,
    sampleBits, BitVec.neg_one_eq_allOnes]
  by_cases he : edge 0 = true <;> by_cases hr : xs ⟨0, by omega⟩ = true <;> simp [he, hr]

theorem memory_next (k w : Nat) (s xs rst edge) (a : BitVec k) :
    (decode k w ((hardware k w).next s (xs,rst) edge)).memory a =
    (AsyncFifo.next (decode k w s) (decodeInput k w xs edge)).memory a := by
  change (cell k w a.toFin).eval (fun _ => false) _ = _
  rw [cell_inputs a.toFin _ (fun _ => false) xs]
  simp only [cell, setWidth_correct]
  rw [word_next]
  have hw : w ≤ bankWidth k w := Nat.le_max_right _ _
  have h0 : 6+a.toNat ≠ 0 := by omega
  have h1 : 6+a.toNat ≠ 1 := by omega
  have h2 : 6+a.toNat ≠ 2 := by omega
  have h3 : 6+a.toNat ≠ 3 := by omega
  have h4 : 6+a.toNat ≠ 4 := by omega
  have h5 : 6+a.toNat ≠ 5 := by omega
  simp only [clock, nextWord, show a.toFin.val = a.toNat from rfl, h0, h1, h2, h3, h4, h5,
    or_self, ↓reduceIte, Nat.add_sub_cancel_left, eval_mux, Expr.eval, equal_correct,
    setWidth_correct, eval_literal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [AsyncFifo.next, ← push_correct k w xs s edge]
  rw [pointer_inputs 0 s xs (fun _ => false)]
  simp only [decode, decodeInput]
  rw [payload_state xs s (fun _ => false)]
  rw [word_inputs _ s xs (fun _ => false)]
  simp only [cell, setWidth_correct, show a.toFin.val = a.toNat from rfl]
  by_cases he : edge 0 = true <;>
    by_cases hp : (push k w).eval xs s = true <;>
    by_cases ha : a = ((pointer k w 0).eval (fun _ => false) s).setWidth k <;>
    simp only [he, hp, ha, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
      ↓reduceIte, beq_self_eq_true, decide_true, BitVec.setWidth_setWidth_of_le _ hw, BitVec.setWidth_eq,
      Bool.false_eq_true, beq_iff_eq, decide_eq_true_eq]
  all_goals first | rfl | simp only [ha, Ne.symm ha, ↓reduceIte]

/-- The actual dual-clock Boolean network implements the model at stable sampling.
Its synchronization uncertainty is separately covered by step_refines_queue. -/
theorem decode_next (k w : Nat) (s xs rst edge) :
    decode k w ((hardware k w).next s (xs,rst) edge) =
      AsyncFifo.next (decode k w s) (decodeInput k w xs edge) := by
  have ext_state {a b : State k w} (hm : a.memory = b.memory) (hw : a.write = b.write)
      (hr : a.read = b.read) (hw1 : a.seenWrite.first = b.seenWrite.first)
      (hw2 : a.seenWrite.second = b.seenWrite.second)
      (hr1 : a.seenRead.first = b.seenRead.first) (hr2 : a.seenRead.second = b.seenRead.second) : a = b := by
    cases a with
    | mk am aw ar asw asr =>
      cases b with
      | mk bm bw br bsw bsr =>
        cases asw; cases asr; cases bsw; cases bsr
        simp_all
  exact ext_state (funext (memory_next k w s xs rst edge))
    (pointer_write_next k w s xs rst edge) (pointer_read_next k w s xs rst edge)
    (sync_write_first_next k w s xs rst edge) (sync_write_second_next k w s xs rst edge)
    (sync_read_first_next k w s xs rst edge) (sync_read_second_next k w s xs rst edge)

theorem read_data_correct (k w : Nat) (s xs) :
    (select (setWidth (pointer k w 1) k) (cell k w)).eval xs s = AsyncFifo.data (decode k w s) := by
  simp only [select_correct, setWidth_correct]
  simp only [pointer_inputs 1 s xs (fun _ => false)]
  exact cell_inputs _ s xs (fun _ => false)

theorem output_ready (k w : Nat) (s xs) :
    (hardware k w).output s xs ⟨0, by omega⟩ = AsyncFifo.enqReady (decode k w s) := by
  simpa [hardware, MultiClock.wordBank, MultiClock.Circuit.output, HDLean.wordBank,
    HDLean.Circuit.evalOutput, output] using ready_correct k w xs s

theorem output_valid (k w : Nat) (s xs) :
    (hardware k w).output s xs ⟨1, by omega⟩ = AsyncFifo.deqValid (decode k w s) := by
  simpa [hardware, MultiClock.wordBank, MultiClock.Circuit.output, HDLean.wordBank,
    HDLean.Circuit.evalOutput, output] using valid_correct k w xs s

theorem output_data (k w : Nat) (s xs) (j : Fin w) :
    (hardware k w).output s xs ⟨2+j.val, by omega⟩ = (AsyncFifo.data (decode k w s)).getLsbD j.val := by
  rw [← read_data_correct k w s xs, WordExpr.eval_bit _ _ _ j.val j.isLt]
  simp [hardware, MultiClock.wordBank, MultiClock.Circuit.output, HDLean.wordBank,
    HDLean.Circuit.evalOutput, output, show ¬(2+j.val < 2) by omega]

/-- Exact storage budget for the current padded word-bank implementation. -/
theorem storage_bits (k w : Nat) :
    (hardware k w).combinational.ffBits = (6+2^k) * max (k+1) w := rfl

/-- Full queue simulation inherited by the emitted network after reset startup. -/
theorem hardware_preserves_queue (k w : Nat) (s xs rst edge) (g : Ghost) (history)
    (hs : g.Safe (2^k)) (hc : g.Controls (decode k w s)) (hm : g.Memory history (decode k w s))
    (hwr : xs ⟨0, by omega⟩ = false) (hrr : xs ⟨1, by omega⟩ = false) :
    ∃ g' : Ghost, g'.Safe (2^k) ∧ g'.Controls (decode k w ((hardware k w).next s (xs,rst) edge)) ∧
      g'.Memory (g.record history (decode k w s) (decodeInput k w xs edge))
        (decode k w ((hardware k w).next s (xs,rst) edge)) := by
  rw [decode_next]
  obtain ⟨g', hs', hc', hm', _⟩ := step_refines_queue (s := decode k w s) (i := decodeInput k w xs edge) hs hc hm hwr hrr
  exact ⟨g', hs', hc', hm'⟩

end HDLean.AsyncFifo.Physical
