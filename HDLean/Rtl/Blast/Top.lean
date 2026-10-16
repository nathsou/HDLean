import HDLean.Rtl.Blast.Reset
import HDLean.Rtl.Blast.ToDag

/-!
# A word-level design as a bit-level node graph

`Design.toDag` bit-blasts the top module of a design (with its whole instance
hierarchy) into a `Dag`, the graph every proved bit-level backend (AIGER,
RTLIL, SystemVerilog) consumes. Input `k` of width `w` becomes `w` input bits
(least significant first, ports in order); the state is `encode d d.top`; the
outputs are the output words' bits, in order.

`toDag_nextState` and `toDag_evalOutput` say the graph simulates the design
cycle for cycle, for every store and every reset level.
-/
namespace HDLean.Rtl.Blast
open Std.Sat Std.Sat.AIG

def wordRegs (ws : List Nat) : List Reg := ws.map fun w => { name := default, width := w, reset := .none, next := 0 }

/-- The bits of words of the given widths, least significant first. -/
def wordsEnc (ws : List Nat) (vs : Array Nat) : List Bool := encRegs (wordRegs ws) 0 (.mk vs #[] #[])

theorem wordsEnc_length (ws : List Nat) (vs : Array Nat) : (wordsEnc ws vs).length = ws.sum := by
  unfold wordsEnc encRegs wordRegs
  suffices ∀ n, ((List.map (fun w => ({ name := default, width := w, reset := .none, next := 0 } : Reg)) ws).zipIdx n
      |>.flatMap fun p => bitsOf p.1.width ((Store.mk vs #[] #[]).regs.getD p.2 0)).length = ws.sum from this 0
  induction ws with
  | nil => simp
  | cons w ws ih => intro n; simp only [List.map_cons, List.zipIdx_cons, List.flatMap_cons, List.length_append,
      bitsOf_length, ih, List.sum_cons]

def concatL : List Bits → Bits
  | [] => #[]
  | b :: bs => b ++ concatL bs

def topInWidths (d : Design) : List Nat := match d.modules[d.top]? with | some m => m.inWidths | none => []
def topOutWidths (d : Design) : List Nat := match d.modules[d.top]? with | some m => m.outWidths | none => []
def topName (d : Design) : String := match d.modules[d.top]? with | some m => m.name.text | none => "top"

def inBits (d : Design) : Nat := (topInWidths d).sum
def outBits (d : Design) : Nat := (topOutWidths d).sum

def toVector (bs : Bits) (n : Nat) : Option (Vector Fanin n) := if h : bs.size = n then some ⟨bs, h⟩ else none

def kindsVector (d : Design) : Vector HDLean.ResetKind (stateBits d d.top) :=
  ⟨(kinds d d.top).toArray, by simp [kinds_length]⟩

/-- Gates and fanins of the whole design. -/
def blastTop (d : Design) : Option ((Array Bits × Bits) × AIG Nat) :=
  let ia := regAtoms 0 (wordRegs (topInWidths d)) AIG.empty
  blastModule d (inBits d) d.top ia.2 ia.1 0

def _root_.HDLean.Rtl.Design.toDag (d : Design) : Option (Dag 0 (inBits d) (stateBits d d.top) (outBits d)) :=
  match blastTop d with
  | some ((outs, next), aig) =>
    if outs.toList.map Array.size = topOutWidths d then
      match toVector next (stateBits d d.top), toVector (concatL outs.toList) (outBits d) with
      | some nv, some ov => Blast.toDag (topName d) aig (inBits d) (stateBits d d.top) (outBits d) nv ov (kindsVector d)
      | _, _ => none
    else none
  | none => none

/-- The state bits of a store. -/
def stateOf (d : Design) (st : Store) : Fin (stateBits d d.top) → Bool := fun k => (encode d d.top st).getD k false

/-- The input bits of input words. -/
def inputsOf (d : Design) (ins : Array Nat) : Fin (inBits d) → Bool := fun k => (wordsEnc (topInWidths d) ins).getD k false

/-- The output bits of output words. -/
def outputsOf (d : Design) (outs : Array Nat) : Fin (outBits d) → Bool :=
  fun k => (wordsEnc (topOutWidths d) outs).getD k false

/-! ## Proofs -/

theorem dn_of_bitIs {aig : AIG Nat} {assign : Nat → Bool} {f : Fanin} {c : Bool} (h : BitIs aig assign f c) :
    dn aig assign f = c := by
  obtain ⟨hb, hd⟩ := h
  simp [dn, hb, hd]

theorem toVector_get {bs : Bits} {n : Nat} {v : Vector Fanin n} (h : toVector bs n = some v) (k : Fin n) :
    v[k] = bs[k.val]'(by unfold toVector at h; split at h <;> simp_all) := by
  unfold toVector at h
  split at h
  · cases h; rfl
  · cases h

theorem concatL_bitsAre {aig : AIG Nat} {assign : Nat → Bool} (vs : Array Nat) :
    ∀ (bs : List Bits) (n : Nat), (∀ i (hi : i < bs.length), RawDen aig assign bs[i] (vs.getD (n + i) 0)) →
      BitsAre aig assign (concatL bs) (((wordRegs (bs.map Array.size)).zipIdx n).flatMap
        fun p => bitsOf p.1.width ((Store.mk vs #[] #[]).regs.getD p.2 0))
  | [], _, _ => by simpa [concatL, wordRegs] using BitsAre.nil aig assign
  | b :: bs, n, h => by
    simp only [concatL, List.map_cons, wordRegs, List.zipIdx_cons, List.flatMap_cons, Store.regs_mk]
    refine BitsAre.append ?_ ?_
    · have := rawden_bitsAre (h 0 (by simp))
      simpa using this
    · have := concatL_bitsAre vs bs (n + 1) (fun i hi => by
        have := h (i + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
      simpa [wordRegs] using this

theorem blastTop_ok (d : Design) (st : Store) (ins : Array Nat) {outs : Array Bits} {next : Bits} {aig : AIG Nat}
    (h : blastTop d = some ((outs, next), aig)) :
    OutsOk aig (assignOf (inBits d) (stateBits d d.top) (inputsOf d ins) (stateOf d st)) outs (d.output st ins) ∧
    BitsAre aig (assignOf (inBits d) (stateBits d d.top) (inputsOf d ins) (stateOf d st)) next
      (encode d d.top (d.sem d.top st ins false).2) := by
  let assign := assignOf (inBits d) (stateBits d d.top) (inputsOf d ins) (stateOf d st)
  have hlen := wordsEnc_length (topInWidths d) ins
  obtain ⟨_, si, di⟩ := regAtoms_ok assign (.mk ins #[] #[]) (wordRegs (topInWidths d)) 0 0 AIG.empty (by
    intro i hi
    have hi' : i < inBits d := by unfold inBits; rw [← hlen]; exact hi
    simp only [Nat.zero_add, assign, assignOf, dite_cond_eq_true (eq_true hi'), inputsOf]
    simp [wordsEnc, List.getD_eq_getElem?_getD, hi])
  have hins : ∀ i, RawDen (regAtoms 0 (wordRegs (topInWidths d)) AIG.empty).2 assign
      ((regAtoms 0 (wordRegs (topInWidths d)) AIG.empty).1.getD i #[]) (ins.getD i 0) := by
    intro i
    by_cases hi : i < (wordRegs (topInWidths d)).length
    · simpa using (di i hi).1
    · rw [getD_size_le _ _ _ (by rw [si]; omega)]; exact RawDen.empty _ _ _
  have hst : Laid assign (inBits d + 0) (encode d d.top st) := by
    intro i hi
    have hi' : i < stateBits d d.top := by rw [← encode_length d d.top st]; exact hi
    simp only [assign, assignOf, Nat.add_zero, show ¬ (inBits d + i < inBits d) by omega, dite_cond_eq_false, not_false_eq_true,
      Nat.add_sub_cancel_left, dite_cond_eq_true (eq_true hi'), stateOf]
  obtain ⟨_, ho, hn⟩ := blastModule_ok d (inBits d) assign d.top _ _ 0 st ins outs next aig h hins hst
  exact ⟨ho, hn⟩

theorem toDag_spec {d : Design} {g : Dag 0 (inBits d) (stateBits d d.top) (outBits d)} (h : d.toDag = some g) :
    ∃ outs next aig nv ov, blastTop d = some ((outs, next), aig) ∧ outs.toList.map Array.size = topOutWidths d ∧
      toVector next (stateBits d d.top) = some nv ∧ toVector (concatL outs.toList) (outBits d) = some ov ∧
      Blast.toDag (topName d) aig (inBits d) (stateBits d d.top) (outBits d) nv ov (kindsVector d) = some g := by
  unfold HDLean.Rtl.Design.toDag at h
  split at h
  · rename_i outs next aig hb
    split at h
    · rename_i hs
      split at h
      · rename_i nv ov h1 h2
        exact ⟨outs, next, aig, nv, ov, hb, hs, h1, h2, h⟩
      · cases h
    · cases h
  · cases h

/-- The bit-level graph steps exactly like the design, for every store, input and reset level. -/
theorem _root_.HDLean.Rtl.Design.toDag_nextState {d : Design} {g : Dag 0 (inBits d) (stateBits d d.top) (outBits d)} (h : d.toDag = some g)
    (st : Store) (ins : Array Nat) (rst : Bool) :
    g.nextState (stateOf d st) (inputsOf d ins, rst) = stateOf d (d.step st (ins, rst)) := by
  obtain ⟨outs, next, aig, nv, ov, hb, _, h1, _, h3⟩ := toDag_spec h
  obtain ⟨_, hn⟩ := blastTop_ok d st ins hb
  funext k
  rw [Blast.toDag_nextState h3, toVector_get h1, dn_of_bitIs (hn.2 k.val _)]
  simp only [kindsVector, Vector.getElem_mk, List.getElem_toArray, stateOf, Design.step]
  rw [(sem_reset d d.top st ins rst).2, applyReset_getD _ _ _ _ _ (by rw [kinds_length]; exact k.isLt)
    (by rw [kinds_length, encode_length]) (by rw [encode_length, encode_length])]
  congr 1
  simp [List.getD_eq_getElem?_getD, k.isLt, kinds_length]

/-- The bit-level graph's outputs are the bits of the design's outputs. -/
theorem _root_.HDLean.Rtl.Design.toDag_evalOutput {d : Design} {g : Dag 0 (inBits d) (stateBits d d.top) (outBits d)} (h : d.toDag = some g)
    (st : Store) (ins : Array Nat) :
    g.evalOutput (stateOf d st) (inputsOf d ins) = outputsOf d (d.output st ins) := by
  obtain ⟨outs, next, aig, nv, ov, hb, hs, _, h2, h3⟩ := toDag_spec h
  obtain ⟨ho, _⟩ := blastTop_ok d st ins hb
  have hc := concatL_bitsAre (aig := aig) (assign := assignOf (inBits d) (stateBits d d.top) (inputsOf d ins)
    (stateOf d st)) (d.output st ins) outs.toList 0 (fun i hi => by
      have := ho.2 i
      simpa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show i < outs.size by simpa using hi)] using this)
  rw [hs] at hc
  funext k
  rw [Blast.toDag_evalOutput h3, toVector_get h2, dn_of_bitIs (hc.2 k.val _)]
  rfl

end HDLean.Rtl.Blast
