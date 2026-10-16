import Designs.Toy16.WordStep
import HDLean.Semantics.Retirement

/-!
# The word-level Toy16 refines the ISA

`npc_eq`, `halt_eq`, `wb_eq` and `store_eq` say the core's decode and execute
logic computes exactly `effectWord` (for every instruction and architectural
state); `step_live` and `step_halted` lift this to a cycle of the design; the
retirement theorem follows from the generic stuttering simulation.
-/
namespace HDLean.Toy16.Word
open HDLean.Rtl HDLean.Rtl.Build

theorem readZ_eq (s : ArchState) (x : BitVec 3) : Hw.readZ s.regs x = s.read x := by
  simp [Hw.readZ, Hw.isZ, ArchState.read, CmpOp.eval]

theorem opc_cases (o : BitVec 4) : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5 ∨ o = 6 ∨ o = 7 ∨ o = 8 ∨ o = 9 ∨
    o = 10 ∨ o = 11 ∨ o = 12 ∨ o = 13 ∨ o = 14 ∨ o = 15 := by
  rcases o with ⟨⟨n, hn⟩⟩
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> simp_all <;> omega

theorem ext08 (x : Word) : x.extractLsb' 0 8 = x.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]

theorem ult_word (x y : Word) : (BitVec.ofBool (x.ult y)).setWidth 16 = if x < y then 1 else 0 := by
  by_cases h : x < y
  · have : x.ult y = true := by simpa [BitVec.ult, BitVec.lt_def] using h
    simp [this, h]
  · have : x.ult y = false := by simpa [BitVec.ult, BitVec.lt_def] using h
    simp [this, h]

theorem npc_eq (i : Word) (s : ArchState) (r : CpuRegs BitVec) (hpc : r.pc = s.pc) :
    Hw.npc i r s.regs = (effectWord i s).nextPc := by
  have hoff : (i.extractLsb' 0 12).setWidth 8 = i.extractLsb' 0 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [BitVec.getLsbD_extractLsb', hj]; omega
  simp only [Hw.npc, Hw.pc1, Hw.isOp, Hw.isHalt, Hw.v, Hw.a, readZ_eq, effectWord, hoff, hpc, Hw.off, Hw.imm,
    Hw.opc, Hw.rd, Hw.rs]
  generalize i.extractLsb' 12 4 = o
  rcases opc_cases o with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [CmpOp.eval]

theorem halt_eq (i : Word) (s : ArchState) : (Hw.isHalt i).getLsbD 0 = (effectWord i s).halt := by
  simp only [Hw.isHalt, effectWord, Hw.opc]
  generalize i.extractLsb' 12 4 = o
  rcases opc_cases o with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [CmpOp.eval]

theorem wb_eq (i : Word) (s : ArchState) :
    (if (Hw.wbe i).getLsbD 0 then some (Hw.rd i, Hw.wbd i s.regs s.dmem
      (aluHw (Hw.opc i) (Hw.a i s.regs) (Hw.bsel i s.regs))) else none) = (effectWord i s).wb := by
  simp only [Hw.wbe, Hw.wbd, Hw.isAlu, Hw.isOp, Hw.isZ, Hw.a, Hw.b, Hw.bsel, Hw.ea, Hw.immS, readZ_eq, ext08, effectWord,
    Hw.opc, Hw.rd, Hw.rs, Hw.rt, Hw.imm]
  generalize i.extractLsb' 12 4 = o
  generalize i.extractLsb' 9 3 = rd
  rcases opc_cases o with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    by_cases hrd : rd = 0 <;> simp [CmpOp.eval, hrd, aluHw, ult_word]

theorem store_eq (i : Word) (s : ArchState) :
    (if (Hw.isOp i 8).getLsbD 0 then some (Hw.ea i s.regs, Hw.v i s.regs) else none) = (effectWord i s).store := by
  simp only [Hw.isOp, Hw.ea, Hw.v, Hw.a, Hw.immS, readZ_eq, ext08, effectWord, Hw.opc, Hw.rd, Hw.rs, Hw.imm]
  generalize i.extractLsb' 12 4 = o
  rcases opc_cases o with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [CmpOp.eval]

/-! ## Architectural view of a store -/

/-- The retirement report held in the registers. -/
def observeRegs (r : CpuRegs BitVec) : Option Retire :=
  if r.valid.getLsbD 0 then
    some { pc := r.rpc, instr := r.rinstr, nextPc := r.rnext,
           wb := if r.wbv.getLsbD 0 then some (r.wbr, r.wbval) else none,
           store := if r.stv.getLsbD 0 then some (r.sta, r.stval) else none,
           halt := r.rhalt.getLsbD 0 }
  else none

def archOf (st : Store) : ArchState :=
  ⟨(regsOfStore st).pc, st.mem 0 3 16, st.mem 1 8 16, (regsOfStore st).halted.getLsbD 0⟩

/-- The instruction bus answers the fetch address with the program word. -/
def fetch (imem : Addr → Word) (st : Store) : Array Nat := #[(imem (regsOfStore st).pc).toNat]

theorem instr_fetch (imem : Addr → Word) (st : Store) : instrOfIns (fetch imem st) = imem (regsOfStore st).pc := by
  show bv 16 ((fetch imem st).getD 0 0) = _
  simp [fetch]

theorem ArchState.ext' {a b : ArchState} (h1 : a.pc = b.pc) (h2 : a.regs = b.regs) (h3 : a.dmem = b.dmem)
    (h4 : a.halted = b.halted) : a = b := by
  cases a; cases b; simp_all

theorem Retire.ext' {a b : Retire} (h1 : a.pc = b.pc) (h2 : a.instr = b.instr) (h3 : a.nextPc = b.nextPc)
    (h4 : a.wb = b.wb) (h5 : a.store = b.store) (h6 : a.halt = b.halt) : a = b := by
  cases a; cases b; simp_all

theorem effectWord_pc (w : Word) (s : ArchState) : (effectWord w s).pc = s.pc := by
  simp only [effectWord]; split <;> rfl

theorem effectWord_instr (w : Word) (s : ArchState) : (effectWord w s).instr = w := by
  simp only [effectWord]; split <;> rfl

theorem observe_out (imem : Addr → Word) (st : Store) (ins : Array Nat) :
    observe (Bundle.decode CpuOut ((design.output st ins).getD · 0)) = observeRegs (regsOfStore st) := by
  rw [output_eq]; simp only [observe, observeRegs, Hw.out]; rfl

/-- A live cycle executes the fetched instruction and reports it. -/
theorem step_live (imem : Addr → Word) (st : Store) (q : ArchState) (hq : archOf st = q) (hl : q.halted = false) :
    let st' := design.step st (fetch imem st, false)
    observeRegs (regsOfStore st') = some (effect imem q) ∧ archOf st' = applyEffect q (effect imem q) := by
  intro st'
  have hr := step_regs st (fetch imem st) false
  rw [Bundle.reset_false, instr_fetch] at hr
  have hpc : (regsOfStore st).pc = q.pc := by rw [← hq]; rfl
  have hh : (regsOfStore st).halted.getLsbD 0 = false := by rw [← hl, ← hq]; rfl
  have hrf : st.mem 0 3 16 = q.regs := by rw [← hq]; rfl
  have hdm : st.mem 1 8 16 = q.dmem := by rw [← hq]; rfl
  have hlive : (Hw.live (regsOfStore st)).getLsbD 0 = true := by
    unfold Hw.live; rw [BitVec.getLsbD_not, hh]; rfl
  have hi : imem (regsOfStore st).pc = imem q.pc := by rw [hpc]
  rw [hi, hrf, hdm] at hr
  have hy : aluNow st (fetch imem st) = aluHw (Hw.opc (imem q.pc)) (Hw.a (imem q.pc) q.regs)
      (Hw.bsel (imem q.pc) q.regs) := by simp only [aluNow, instr_fetch, hi, hrf]
  rw [hy] at hr
  have hwb := wb_eq (imem q.pc) q
  have hst := store_eq (imem q.pc) q
  have hnpc := npc_eq (imem q.pc) q (regsOfStore st) hpc
  have hhalt := halt_eq (imem q.pc) q
  constructor
  · show observeRegs (regsOfStore st') = _
    rw [hr]
    simp only [observeRegs, Hw.next, hlive, ite_true, effect]
    congr 1
    exact Retire.ext' (by rw [effectWord_pc, hpc]) (by rw [effectWord_instr]) hnpc hwb hst hhalt
  · show archOf st' = _
    have hand : ∀ x : BitVec 1, (Hw.live (regsOfStore st) &&& x).getLsbD 0 = x.getLsbD 0 := by
      intro x; rw [BitVec.getLsbD_and, hlive, Bool.true_and]
    refine ArchState.ext' ?_ ?_ ?_ ?_
    · show (regsOfStore st').pc = _
      rw [hr]
      simp only [Hw.next, hlive, ite_true, applyEffect, effect]
      exact hnpc
    · funext a
      show st'.mem 0 3 16 a = _
      rw [step_rf, hand, instr_fetch, hi, hrf, hdm, hy]
      simp only [applyEffect, effect, ← hwb]
      by_cases hw : (Hw.wbe (imem q.pc)).getLsbD 0 = true
      · simp only [hw, true_and, ite_true]
        by_cases ha : Hw.rd (imem q.pc) = a
        · simp [ha]
        · simp [ha, Ne.symm ha]
      · simp only [hw, Bool.false_eq_true, false_and, ite_false, if_false]
    · funext a
      show st'.mem 1 8 16 a = _
      rw [step_dm, hand, instr_fetch, hi, hrf, hdm]
      simp only [applyEffect, effect, ← hst]
      by_cases hw : (Hw.isOp (imem q.pc) 8).getLsbD 0 = true
      · simp only [hw, true_and, ite_true]
        by_cases ha : Hw.ea (imem q.pc) q.regs = a
        · simp [ha]
        · simp [ha, Ne.symm ha]
      · simp only [hw, Bool.false_eq_true, false_and, ite_false, if_false]
    · show (regsOfStore st').halted.getLsbD 0 = _
      rw [hr]
      simp only [Hw.next, applyEffect, effect, BitVec.getLsbD_or, hh, Bool.false_or]
      exact hhalt

/-- A halted core keeps its architectural state and reports nothing. -/
theorem step_halted (imem : Addr → Word) (st : Store) (q : ArchState) (hq : archOf st = q) (hl : q.halted = true) :
    let st' := design.step st (fetch imem st, false)
    observeRegs (regsOfStore st') = none ∧ archOf st' = q := by
  intro st'
  have hr := step_regs st (fetch imem st) false
  rw [Bundle.reset_false] at hr
  have hh : (regsOfStore st).halted.getLsbD 0 = true := by rw [← hl, ← hq]; rfl
  have hlive : (Hw.live (regsOfStore st)).getLsbD 0 = false := by
    unfold Hw.live; rw [BitVec.getLsbD_not, hh]; rfl
  have hand : ∀ x : BitVec 1, (Hw.live (regsOfStore st) &&& x).getLsbD 0 = false := by
    intro x; rw [BitVec.getLsbD_and, hlive, Bool.false_and]
  constructor
  · show observeRegs (regsOfStore st') = _
    rw [hr]
    simp only [observeRegs, Hw.next, hlive, Bool.false_eq_true, ite_false]
  · rw [← hq]
    refine ArchState.ext' ?_ ?_ ?_ ?_
    · show (regsOfStore st').pc = _
      rw [hr]
      simp only [Hw.next, hlive, Bool.false_eq_true, ite_false]
      rfl
    · funext a
      show st'.mem 0 3 16 a = _
      rw [step_rf, hand]
      simp only [Bool.false_eq_true, false_and, ite_false]
      rfl
    · funext a
      show st'.mem 1 8 16 a = _
      rw [step_dm, hand]
      simp only [Bool.false_eq_true, false_and, ite_false]
      rfl
    · show (regsOfStore st').halted.getLsbD 0 = _
      rw [hr]
      simp only [Hw.next, BitVec.getLsbD_or, hh, Bool.true_or]
      exact hh.symm

/-- From any store with architectural view `q`, the next cycle is related to `q`. -/
def Rel (imem : Addr → Word) (st : Store) (q : ArchState) : Prop :=
  ((regsOfStore st).valid.getLsbD 0 = false ∧ archOf st = q) ∨
  ((regsOfStore st).valid.getLsbD 0 = true ∧ q.halted = false ∧ observeRegs (regsOfStore st) = some (effect imem q) ∧
    archOf st = applyEffect q (effect imem q))

theorem valid_of_observe {r : CpuRegs BitVec} {a : Retire} (h : observeRegs r = some a) : r.valid.getLsbD 0 = true := by
  unfold observeRegs at h; split at h
  · assumption
  · cases h

theorem observe_none {r : CpuRegs BitVec} (h : r.valid.getLsbD 0 = false) : observeRegs r = none := by
  unfold observeRegs; rw [if_neg (by rw [h]; decide)]

theorem rel_next (imem : Addr → Word) (st : Store) (q : ArchState) (hq : archOf st = q) :
    Rel imem (design.step st (fetch imem st, false)) q := by
  cases hl : q.halted
  · obtain ⟨h1, h2⟩ := step_live imem st q hq hl
    exact Or.inr ⟨valid_of_observe h1, hl, h1, h2⟩
  · obtain ⟨h1, h2⟩ := step_halted imem st q hq hl
    refine Or.inl ⟨?_, h2⟩
    cases hv : (regsOfStore (design.step st (fetch imem st, false))).valid.getLsbD 0
    · rfl
    · simp [observeRegs, hv] at h1

/-! ## Control facts used for progress -/

theorem next_regs (imem : Addr → Word) (st : Store) :
    regsOfStore (design.step st (fetch imem st, false)) = Hw.next (imem (regsOfStore st).pc) (regsOfStore st)
      (st.mem 0 3 16) (st.mem 1 8 16) (aluNow st (fetch imem st)) := by
  rw [step_regs, Bundle.reset_false, instr_fetch]

theorem next_valid (imem : Addr → Word) (st : Store) :
    (regsOfStore (design.step st (fetch imem st, false))).valid.getLsbD 0 = !(regsOfStore st).halted.getLsbD 0 := by
  rw [next_regs]; simp only [Hw.next, Hw.live, BitVec.getLsbD_not]; rfl

theorem next_halted (imem : Addr → Word) (st : Store) :
    (regsOfStore (design.step st (fetch imem st, false))).halted.getLsbD 0 =
      ((regsOfStore st).halted.getLsbD 0 || (Hw.isHalt (imem (regsOfStore st).pc)).getLsbD 0) := by
  rw [next_regs]; simp only [Hw.next, BitVec.getLsbD_or]

theorem next_rhalt (imem : Addr → Word) (st : Store) :
    (regsOfStore (design.step st (fetch imem st, false))).rhalt = Hw.isHalt (imem (regsOfStore st).pc) := by
  rw [next_regs]; rfl

/-- After reset: fetch from address zero, not halted, nothing to report. -/
theorem reset_regs (st : Store) (ins : Array Nat) :
    (regsOfStore (design.step st (ins, true))).pc = 0 ∧
    (regsOfStore (design.step st (ins, true))).halted.getLsbD 0 = false ∧
    (regsOfStore (design.step st (ins, true))).valid.getLsbD 0 = false := by
  rw [step_regs]
  simp [Bundle.reset, resets, Bundle.toVec, Bundle.ofVec, HVec.zipWith, resetField, bv]

theorem fetchOut_eq (imem : Addr → Word) (st : Store) : fetchOut design imem st = fetch imem st := by
  have h := congrArg CpuOut.pc (output_eq st #[])
  simp only [fetchOut, fetch, outputsOf, h]
  rfl

theorem outputsOf_eq (st : Store) : observe (outputsOf design st) = observeRegs (regsOfStore st) :=
  observe_out (fun _ => 0) st #[]

end HDLean.Toy16.Word
