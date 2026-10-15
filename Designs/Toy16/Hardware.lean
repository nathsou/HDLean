import Designs.Toy16.Core
import HDLean.Core.WordBank
import HDLean.Lib.MemoryCircuit
import HDLean.Netlist.Lower

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace HDLean.Toy16.Physical
open WordExpr

/-- Uniform 16-bit bank: PC, halted, execute, fetched instruction, eight registers,
and 256 data words. Narrow controls use their low bits. -/
abbrev W (n : Nat) := WordExpr 0 0 (268*16) n
abbrev E := Expr 0 0 (268*16)

def word (j : Fin 268) : W 16 := bankWord j

def pc : W 8 := extract (word ⟨0, by decide⟩) 0 8 (by decide)
def halted : E := (word ⟨1, by decide⟩)[0]
def execute : E := (word ⟨2, by decide⟩)[0]
def fetched : W 16 := word ⟨3, by decide⟩

def regWord (j : Fin 8) : W 16 := word ⟨4+j.val, by omega⟩
def memWord (j : Fin 256) : W 16 := word ⟨12+j.val, by omega⟩
def readReg (a : W 3) : W 16 := select a (fun j => if j.val = 0 then literal 0 else regWord j)

def rd : W 3 := extract fetched 9 3 (by decide)
def rs : W 3 := extract fetched 6 3 (by decide)
def rt : W 3 := extract fetched 3 3 (by decide)
def opcode : W 4 := extract fetched 12 4 (by decide)
def imm : W 6 := extract fetched 0 6 (by decide)
def offset : W 12 := extract fetched 0 12 (by decide)
def operandA : W 16 := readReg rs
def operandB : W 16 := readReg rt
def storeData : W 16 := readReg rd
def ea : W 8 := WordExpr.setWidth (add operandA (WordExpr.signExtend imm 16)) 8
def isOp (n : Nat) : E := equal opcode (literal (BitVec.ofNat 4 n))
def flagWord (b : E) : W 16 := mux b (literal 1) (literal 0)
def trap : E := .inv (ult opcode (literal 11))

def result : W 16 := select opcode fun j => match j.val with
  | 0 => add operandA operandB
  | 1 => sub operandA operandB
  | 2 => bitAnd operandA operandB
  | 3 => bitOr operandA operandB
  | 4 => bitXor operandA operandB
  | 5 => flagWord (ult operandA operandB)
  | 6 => add operandA (WordExpr.signExtend imm 16)
  | 7 => select ea memWord
  | _ => literal 0

def nextPc : W 8 :=
  mux trap pc (mux (isOp 10) (add (add pc (literal 1)) (WordExpr.setWidth offset 8))
    (mux (.and (isOp 9) (equal storeData operandA))
      (add (add pc (literal 1)) (WordExpr.signExtend imm 8)) (add pc (literal 1))))
def writeEnable : E := .and (ult opcode (literal 8)) (.inv (equal rd (literal 0)))
def active : E := .and execute (.inv halted)

def resetKind (j : Fin 268) : ResetKind := if j.val < 3 then .synchronous false else .hold

def nextWord (imem : Addr → Word) (j : Fin 268) : W 16 :=
  if j.val = 0 then mux active (WordExpr.setWidth nextPc 16) (word j)
  else if j.val = 1 then mux active (flagWord trap) (word j)
  else if j.val = 2 then mux halted (word j) (flagWord (.inv execute))
  else if j.val = 3 then mux (.and (.inv halted) (.inv execute))
    (select pc (fun a => literal (imem (BitVec.ofNat 8 a.val)))) (word j)
  else if j.val < 12 then
    mux (.and active (.and writeEnable (equal rd (literal (BitVec.ofNat 3 (j.val-4)))))) result (word j)
  else mux (.and active (.and (isOp 8) (equal ea (literal (BitVec.ofNat 8 (j.val-12))))))
    storeData (word j)

def outputBits : Vector E 79 := Vector.ofFn fun k =>
  if h : k.val = 0 then active
  else if h : k.val < 9 then pc[ k.val-1 ]' (by omega)
  else if h : k.val < 25 then fetched[ k.val-9 ]' (by omega)
  else if h : k.val < 33 then nextPc[ k.val-25 ]' (by omega)
  else if h : k.val = 33 then writeEnable
  else if h : k.val < 37 then rd[ k.val-34 ]' (by omega)
  else if h : k.val < 53 then result[ k.val-37 ]' (by omega)
  else if h : k.val = 53 then isOp 8
  else if h : k.val < 62 then ea[ k.val-54 ]' (by omega)
  else if h : k.val < 78 then storeData[ k.val-62 ]' (by omega)
  else trap

/-- Physical serialized fetch/execute core. All payload storage is unreset. -/
def hardware (imem : Addr → Word) : Circuit 0 0 (268*16) 79 :=
  wordBank "toy16" resetKind (nextWord imem) outputBits

def decode (s : Fin (268*16) → Bool) : CoreState :=
  { arch := { pc := pc.eval Fin.elim0 s
              halted := halted.eval Fin.elim0 s
              regs := fun r => (regWord r.toFin).eval Fin.elim0 s
              dmem := fun a => (memWord a.toFin).eval Fin.elim0 s }
    fetched := fetched.eval Fin.elim0 s
    execute := execute.eval Fin.elim0 s }

@[simp] theorem readReg_correct (a : W 3) (s) :
    (readReg a).eval Fin.elim0 s = (decode s).arch.read (a.eval Fin.elim0 s) := by
  simp [readReg, select_correct, ArchState.read, decode]
  have he : (a.eval Fin.elim0 s).toFin = 0 ↔ a.eval Fin.elim0 s = 0 := by
    constructor
    · intro h; exact BitVec.eq_of_toFin_eq h
    · intro h; rw [h]; rfl
  simp only [he]
  split <;> simp_all

@[simp] theorem readReg_eval (a : W 3) (s) :
    (readReg a).eval Fin.elim0 s =
      if a.eval Fin.elim0 s = 0 then 0 else (regWord (a.eval Fin.elim0 s).toFin).eval Fin.elim0 s := by
  simpa only [ArchState.read, decode] using readReg_correct a s

def evaluatedEffect (s : Fin (268*16) → Bool) : Retire :=
  { pc := pc.eval Fin.elim0 s
    instr := fetched.eval Fin.elim0 s
    nextPc := nextPc.eval Fin.elim0 s
    wb := if writeEnable.eval Fin.elim0 s then
      some (rd.eval Fin.elim0 s, result.eval Fin.elim0 s) else none
    store := if (isOp 8).eval Fin.elim0 s then
      some (ea.eval Fin.elim0 s, storeData.eval Fin.elim0 s) else none
    halt := trap.eval Fin.elim0 s }

private theorem op_toNat (s : Fin (268*16) → Bool) :
    (opcode.eval Fin.elim0 s).toNat = ((decode s).fetched.extractLsb' 12 4).toNat := by
  simp [opcode, decode]

theorem effect_correct (s : Fin (268*16) → Bool) :
    evaluatedEffect s = effectWord (decode s).fetched (decode s).arch := by
  have bound := (opcode.eval Fin.elim0 s).isLt
  have hc : (opcode.eval Fin.elim0 s).toNat = 0 ∨
    (opcode.eval Fin.elim0 s).toNat = 1 ∨ (opcode.eval Fin.elim0 s).toNat = 2 ∨
    (opcode.eval Fin.elim0 s).toNat = 3 ∨ (opcode.eval Fin.elim0 s).toNat = 4 ∨
    (opcode.eval Fin.elim0 s).toNat = 5 ∨ (opcode.eval Fin.elim0 s).toNat = 6 ∨
    (opcode.eval Fin.elim0 s).toNat = 7 ∨ (opcode.eval Fin.elim0 s).toNat = 8 ∨
    (opcode.eval Fin.elim0 s).toNat = 9 ∨ (opcode.eval Fin.elim0 s).toNat = 10 ∨
    (opcode.eval Fin.elim0 s).toNat = 11 ∨ (opcode.eval Fin.elim0 s).toNat = 12 ∨
    (opcode.eval Fin.elim0 s).toNat = 13 ∨ (opcode.eval Fin.elim0 s).toNat = 14 ∨
    (opcode.eval Fin.elim0 s).toNat = 15 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    have hv := congrArg (BitVec.ofNat 4) h
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hv
    have ho := h
    rw [op_toNat] at ho
    simp only [evaluatedEffect, effectWord, ← op_toNat, h]
    simp [nextPc, trap, isOp, writeEnable, result, flagWord, select_correct,
      operandA, operandB, storeData, ea, WordExpr.ult_correct, Expr.eval,
      BitVec.lt_def, hv, readReg_eval, ArchState.read, rd, rs, rt, imm, offset, decode,
      WordExpr.extract_correct]
  all_goals try simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
  all_goals simp only [Fin.ofNat, Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 65536)]
  all_goals rfl

theorem word_next (imem : Addr → Word) (s rst) (j : Fin 268) :
    (word j).eval Fin.elim0 ((hardware imem).next s (Fin.elim0,rst)) =
      if rst then if j.val < 3 then 0 else (word j).eval Fin.elim0 s
      else (nextWord imem j).eval Fin.elim0 s := by
  change (bankWord j).eval Fin.elim0 ((wordBank "toy16" resetKind (nextWord imem) outputBits).next s _) = _
  rw [wordBank_next]
  unfold resetKind
  by_cases hj : j.val < 3 <;> simp [hj, word]

@[simp] theorem flagWord_eval (b : E) (s) :
    (flagWord b).eval Fin.elim0 s = if b.eval Fin.elim0 s then 1 else 0 := by
  simp [flagWord]

private theorem low_flag (b : E) (s) :
    ((flagWord b).eval Fin.elim0 s).getLsbD 0 = b.eval Fin.elim0 s := by
  cases h : b.eval Fin.elim0 s <;> simp [flagWord_eval, h]

private theorem halted_bit (s) : halted.eval Fin.elim0 s = ((word ⟨1, by decide⟩).eval Fin.elim0 s).getLsbD 0 :=
  (WordExpr.eval_bit _ _ _ 0 (by decide)).symm
private theorem execute_bit (s) : execute.eval Fin.elim0 s = ((word ⟨2, by decide⟩).eval Fin.elim0 s).getLsbD 0 :=
  (WordExpr.eval_bit _ _ _ 0 (by decide)).symm

@[simp] private theorem numeral_index (n : Nat) :
    (@OfNat.ofNat (Fin 268) n inferInstance).val = n % 268 := rfl

@[simp] private theorem index_zero : (0 : Fin 268).val = 0 := rfl
@[simp] private theorem index_one : (1 : Fin 268).val = 1 := rfl
@[simp] private theorem index_two : (2 : Fin 268).val = 2 := rfl
@[simp] private theorem index_three : (3 : Fin 268).val = 3 := rfl
@[simp] private theorem halted_low (s) : ((word (1 : Fin 268)).eval Fin.elim0 s)[0] = halted.eval Fin.elim0 s := by
  exact WordExpr.eval_bit _ _ _ 0 (by decide)
@[simp] private theorem execute_low (s) : ((word (2 : Fin 268)).eval Fin.elim0 s)[0] = execute.eval Fin.elim0 s := by
  exact WordExpr.eval_bit _ _ _ 0 (by decide)

private theorem nextWord_reg (imem : Addr → Word) (j : Fin 8) :
    nextWord imem ⟨4+j.val, by omega⟩ =
      mux (.and active (.and writeEnable (equal rd (literal (BitVec.ofNat 3 j.val)))))
        result (regWord j) := by
  have hj := j.isLt
  have h1 : 4+j.val ≠ 1 := by omega
  have h2 : 4+j.val ≠ 2 := by omega
  have h3 : 4+j.val ≠ 3 := by omega
  have h12 : 4+j.val < 12 := by omega
  simp [nextWord, regWord, h1, h2, h3, h12]

private theorem nextWord_mem (imem : Addr → Word) (j : Fin 256) :
    nextWord imem ⟨12+j.val, by omega⟩ =
      mux (.and active (.and (isOp 8) (equal ea (literal (BitVec.ofNat 8 j.val)))))
        storeData (memWord j) := by
  have hj := j.isLt
  have h1 : 12+j.val ≠ 1 := by omega
  have h2 : 12+j.val ≠ 2 := by omega
  have h3 : 12+j.val ≠ 3 := by omega
  have h12 : ¬12+j.val < 12 := by omega
  simp [nextWord, memWord, h1, h2, h3, h12]

@[simp] private theorem register_not_control (n : Nat) : ¬4+n < 3 := by omega
@[simp] private theorem memory_not_control (n : Nat) : ¬12+n < 3 := by omega
@[simp] private theorem flag_low (b : Bool) : ((if b then (1 : BitVec 16) else 0))[0] = b := by
  cases b <;> decide

@[simp] private theorem optional_write [DecidableEq α] (en : Bool) (addr k : α) (v : β) (s : α → β) :
    (match (if en then some (addr,v) else none) with
      | some (a,x) => if k = a then x else s k
      | none => s k) = if en = true ∧ addr = k then v else s k := by
  cases en <;> simp [eq_comm]

theorem decode_next (imem : Addr → Word) (s rst) :
    decode ((hardware imem).next s (Fin.elim0,rst)) = (core imem).next (decode s) rst := by
  simp only [core]
  rw [← effect_correct]
  have hhbit : ((word ⟨1,by decide⟩).eval Fin.elim0 s)[0] = halted.eval Fin.elim0 s := by
    exact halted_low s
  have hebit : ((word ⟨2,by decide⟩).eval Fin.elim0 s)[0] = execute.eval Fin.elim0 s := by
    exact execute_low s
  cases hr : rst <;> cases hh : halted.eval Fin.elim0 s <;> cases he : execute.eval Fin.elim0 s
  all_goals
    simp only [decode, hr, hh, he, Bool.false_eq_true, ↓reduceIte]
    congr 1
  all_goals
    try simp only [regWord, memWord, word_next, nextWord_reg, nextWord_mem]
    simp (disch := omega) [pc, fetched, halted_bit, execute_bit, word_next, nextWord, hr, hh, he,
      active, Expr.eval, hhbit, hebit, low_flag, numeral_index, flagWord_eval, WordExpr.select_correct,
      evaluatedEffect, applyEffect, decode, regWord, memWord, ArchState.atReset, Fin.instOfNat, Fin.ofNat]

  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try (apply funext; intro j)
  all_goals try simp (disch := omega) [hr, hh, he, index_one, index_two, index_three,
    halted_low, execute_low, optional_write, register_not_control, memory_not_control, flag_low]

  · congr 1
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hk16 : k < 16 := by omega
    simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hk, hk16]
  · cases h : writeEnable.eval Fin.elim0 s <;> simp [h, eq_comm]
  · cases h : (isOp 8).eval Fin.elim0 s <;> simp [h, eq_comm]
  · cases h : trap.eval Fin.elim0 s <;> simp [h]

/-- Decode the emitted retirement bus; invalid fields are intentionally ignored. -/
def readOutput (bits : Fin 79 → Bool) (offset width : Nat) (h : offset+width ≤ 79) : BitVec width :=
  (WordExpr.inputs offset h : WordExpr 0 79 0 width).eval bits Fin.elim0

def observe (bits : Fin 79 → Bool) : Option Retire :=
  if bits 0 then some
    { pc := readOutput bits 1 8 (by decide)
      instr := readOutput bits 9 16 (by decide)
      nextPc := readOutput bits 25 8 (by decide)
      wb := if bits 33 then some (readOutput bits 34 3 (by decide), readOutput bits 37 16 (by decide)) else none
      store := if bits 53 then some (readOutput bits 54 8 (by decide), readOutput bits 62 16 (by decide)) else none
      halt := bits 78 } else none

private theorem readOutput_word (imem : Addr → Word) (s) (off n : Nat) (h : off+n ≤ 79)
    (value : W n) (hb : ∀ k : Fin n, outputBits[off+k.val] = value[k]) :
    readOutput ((hardware imem).evalOutput s Fin.elim0) off n h = value.eval Fin.elim0 s := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  unfold readOutput
  rw [WordExpr.eval_bit _ _ _ k hk, WordExpr.eval_bit _ _ _ k hk]
  simpa only [WordExpr.inputs, Vector.getElem_ofFn, Expr.eval, Circuit.evalOutput, hardware, wordBank, Fin.getElem_fin] using
    congrArg (Expr.eval Fin.elim0 s) (hb ⟨k,hk⟩)

@[simp] private theorem port_33 : (33 : Fin 79).val = 33 := rfl
@[simp] private theorem port_53 : (53 : Fin 79).val = 53 := rfl
@[simp] private theorem port_78 : (78 : Fin 79).val = 78 := rfl

theorem decode_output (imem : Addr → Word) (s) :
    observe ((hardware imem).evalOutput s Fin.elim0) = (core imem).out (decode s) := by
  have hw (off n : Nat) (h : off+n ≤ 79) (value : W n)
      (hb : ∀ k : Fin n, outputBits[off+k.val] = value[k]) := readOutput_word imem s off n h value hb
  have hpc := hw 1 8 (by decide) pc (by
    intro k
    have hk := k.isLt
    have h0 : ¬(1+k.val = 0) := by omega
    have h1 : 1+k.val < 9 := by omega
    simp only [outputBits, Vector.getElem_ofFn, h0, h1, ↓reduceDIte]
    congr 1 <;> omega)
  have hf := hw 9 16 (by decide) fetched (by
    intro k
    have hk := k.isLt
    have h0 : ¬(9+k.val = 0) := by omega
    have h1 : ¬(9+k.val < 9) := by omega
    have h2 : 9+k.val < 25 := by omega
    simp only [outputBits, Vector.getElem_ofFn, h0, h1, h2, ↓reduceDIte]
    congr 1 <;> omega)
  have hn := hw 25 8 (by decide) nextPc (by
    intro k
    have hk := k.isLt
    have h0 : ¬(25+k.val = 0) := by omega
    have h1 : ¬(25+k.val < 9) := by omega
    have h2 : ¬(25+k.val < 25) := by omega
    have h3 : 25+k.val < 33 := by omega
    simp only [outputBits, Vector.getElem_ofFn, h0, h1, h2, h3, ↓reduceDIte]
    congr 1 <;> omega)
  have hr := hw 34 3 (by decide) rd (by
    intro k
    have hk := k.isLt
    have h0 : ¬(34+k.val = 0) := by omega
    have h1 : ¬(34+k.val < 9) := by omega
    have h2 : ¬(34+k.val < 25) := by omega
    have h3 : ¬(34+k.val < 33) := by omega
    have h4 : ¬(34+k.val = 33) := by omega
    have h5 : 34+k.val < 37 := by omega
    simp only [outputBits, Vector.getElem_ofFn, h0, h1, h2, h3, h4, h5, ↓reduceDIte]
    congr 1 <;> omega)
  have hv := hw 37 16 (by decide) result (by
    intro k
    have hk := k.isLt
    have h0 : ¬(37+k.val = 0) := by omega
    have h1 : ¬(37+k.val < 9) := by omega
    have h2 : ¬(37+k.val < 25) := by omega
    have h3 : ¬(37+k.val < 33) := by omega
    have h4 : ¬(37+k.val = 33) := by omega
    have h5 : ¬(37+k.val < 37) := by omega
    have h6 : 37+k.val < 53 := by omega
    simp only [outputBits, Vector.getElem_ofFn, h0, h1, h2, h3, h4, h5, h6, ↓reduceDIte]
    congr 1 <;> omega)
  have ha := hw 54 8 (by decide) ea (by
    intro k
    have hk := k.isLt
    have h0 : ¬(54+k.val = 0) := by omega
    have h1 : ¬(54+k.val < 9) := by omega
    have h2 : ¬(54+k.val < 25) := by omega
    have h3 : ¬(54+k.val < 33) := by omega
    have h4 : ¬(54+k.val = 33) := by omega
    have h5 : ¬(54+k.val < 37) := by omega
    have h6 : ¬(54+k.val < 53) := by omega
    have h7 : ¬(54+k.val = 53) := by omega
    have h8 : 54+k.val < 62 := by omega
    simp only [outputBits, Vector.getElem_ofFn, h0, h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceDIte]
    congr 1 <;> omega)
  have hd := hw 62 16 (by decide) storeData (by
    intro k
    have hk := k.isLt
    have h0 : ¬(62+k.val = 0) := by omega
    have h1 : ¬(62+k.val < 9) := by omega
    have h2 : ¬(62+k.val < 25) := by omega
    have h3 : ¬(62+k.val < 33) := by omega
    have h4 : ¬(62+k.val = 33) := by omega
    have h5 : ¬(62+k.val < 37) := by omega
    have h6 : ¬(62+k.val < 53) := by omega
    have h7 : ¬(62+k.val = 53) := by omega
    have h8 : ¬(62+k.val < 62) := by omega
    have h9 : 62+k.val < 78 := by omega
    simp only [outputBits, Vector.getElem_ofFn, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, ↓reduceDIte]
    congr 1 <;> omega)
  change observe ((hardware imem).evalOutput s Fin.elim0) =
    if active.eval Fin.elim0 s then some (effectWord (decode s).fetched (decode s).arch) else none
  rw [← effect_correct]
  simp only [observe, evaluatedEffect, hpc, hf, hn, hr, hv, ha, hd]
  simp [hpc,hf,hn,hr,hv,ha,hd,Circuit.evalOutput,hardware,wordBank,outputBits,active,Expr.eval]

theorem hardware_moore (imem : Addr → Word) : (hardware imem).IsMoore := by
  intro s a b
  have h : a = b := by funext k; nomatch k
  rw [h]

/-- Bit-level storage implements every serialized-core state transition, from
arbitrary power-up values and with reset sampled on the physical clock. -/
theorem hardware_state (imem : Addr → Word) (s₀) (rst : Nat → Bool) (t : Nat) :
    decode (((hardware imem).denote (hardware_moore imem)).stateFrom s₀ (fun n => (Fin.elim0,rst n)) t) =
      (core imem).stateFrom (decode s₀) rst t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [PMachine.stateFrom_succ]
    change decode ((hardware imem).next _ (Fin.elim0,rst t)) = _
    rw [decode_next, ih]

theorem hardware_trace (imem : Addr → Word) (s₀) (rst : Nat → Bool) (t : Nat) :
    observe (((hardware imem).denote (hardware_moore imem)).runFrom s₀ (fun n => (Fin.elim0,rst n)) t) =
      (core imem).runFrom (decode s₀) rst t := by
  unfold PMachine.runFrom
  have hx : (fun _ : Fin 0 => false) = Fin.elim0 := by funext k; nomatch k
  simp only [Circuit.denote, hx]
  rw [decode_output]
  have hs := hardware_state imem s₀ rst t
  simp only [Circuit.denote, hx] at hs
  rw [hs]

/-- End-to-end retirement and progress on the physical, emitted retirement bus. -/
theorem hardware_correct (imem : Addr → Word) (s₀) (rst : Nat → Bool)
    (hr : rst 0 = true) (hd : ∀ t, 0 < t → rst t = false) :
    ∃ regs mem,
      let retire := fun t => observe (((hardware imem).denote (hardware_moore imem)).runFrom
        s₀ (fun n => (Fin.elim0,rst n)) (t+1))
      RetiresLike retire (isaRetire imem (ArchState.atReset regs mem)) ∧ Progress 2 retire Retire.halt := by
  simpa only [hardware_trace] using core_correct imem (decode s₀) rst hr hd

/-- All storage is explicit. Narrow controls deliberately retain 30 unused bits;
this count is a measured implementation budget rather than an ISA requirement. -/
theorem ffBits (imem : Addr → Word) : (lower (hardware imem)).ffBits = 4288 := rfl

end HDLean.Toy16.Physical
