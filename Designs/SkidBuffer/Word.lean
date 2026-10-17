import Designs.Fifo.Word
import Designs.PipelineRtl.Interface

/-!
# The three-stage pipeline in word-level RTL

One module holding three two-entry stages, each built by the same stage
functions as the FIFO (`Fifo.Word.flags`, `Fifo.Word.advance`). Every stage's
flags are computed from the registers first; then each stage advances with its
neighbours' valid and ready, so the valid/ready loop never goes through
combinational logic.
-/
namespace HDLean.SkidBuffer.Word
open HDLean.Rtl HDLean.Rtl.Build HDLean.Fifo HDLean.Fifo.Word

hdl_record Regs (w : Nat) where
  count0 : 2
  head0 : w
  tail0 : w
  count1 : 2
  head1 : w
  tail1 : w
  count2 : 2
  head2 : w
  tail2 : w

def ctx (w : Nat) : Ctx :=
  Ctx.mealy "pipeline" (Fifo.Word.In w) (Out w) (Regs w) ⟨.sync 0, .none, .none, .sync 0, .none, .none, .sync 0, .none, .none⟩ #[]

def body (i : Fifo.Word.In w Sig) (r : Regs w Sig) : M (ctx w) (Step (Out w) (Regs w)) := do
  let f0 ← flags r.count0
  let f1 ← flags r.count1
  let f2 ← flags r.count2
  let n0 ← advance f0 i.enqValid f1.ready i.data r.count0 r.head0 r.tail0
  let n1 ← advance f1 f0.valid f2.ready r.head0 r.count1 r.head1 r.tail1
  let n2 ← advance f2 f1.valid i.deqReady r.head1 r.count2 r.head2 r.tail2
  pure { out := ⟨f0.ready, f0.valid, r.head0, f1.ready, f1.valid, r.head1, f2.ready, f2.valid, r.head2⟩
         next := ⟨n0.1, n0.2.1, n0.2.2, n1.1, n1.2.1, n1.2.2, n2.1, n2.2.1, n2.2.2⟩ }

def program (w : Nat) : M (ctx w) Wiring := mealy (Fifo.Word.In w) (Out w) (Regs w) body

def design (w : Nat) : Design := ⟨#[(ctx w).module (program w)]⟩

/-! ## The design as functions of records -/

def decIn (w : Nat) (e : Env) : Fifo.Word.In w BitVec := Bundle.decode (Fifo.Word.In w) (e.ins.getD · 0)
def decRegs (w : Nat) (e : Env) : Regs w BitVec := Bundle.decode (Regs w) (e.st.regs.getD · 0)

def ready (c : BitVec 2) : BitVec 1 := ~~~(BitVec.ofBool (c == 2))
def valid (c : BitVec 2) : BitVec 1 := ~~~(BitVec.ofBool (c == 0))

def outOf (r : Regs w BitVec) : Out w BitVec :=
  ⟨ready r.count0, valid r.count0, r.head0, ready r.count1, valid r.count1, r.head1,
   ready r.count2, valid r.count2, r.head2⟩

def stepOf (i : Fifo.Word.In w BitVec) (r : Regs w BitVec) : Regs w BitVec :=
  let n0 := advanceOf i.enqValid (ready r.count1) i.data r.count0 r.head0 r.tail0
  let n1 := advanceOf (valid r.count0) (ready r.count2) r.head0 r.count1 r.head1 r.tail1
  let n2 := advanceOf (valid r.count1) i.deqReady r.head1 r.count2 r.head2 r.tail2
  ⟨n0.1, n0.2.1, n0.2.2, n1.1, n1.2.1, n1.2.2, n2.1, n2.2.1, n2.2.2⟩

theorem ctx_ok (w : Nat) (hw : 0 < w) : (ctx w).ok = true := by
  simp [Ctx.ok, ctx, Ctx.mealy, Bundle.ports, Bundle.fields, Bundle.toVec, HVec.toList, Reset.fits, hw]

theorem body_ensures (w : Nat) (hw : 0 < w) (s : State (ctx w)) (i : Fifo.Word.In w Sig) (r : Regs w Sig)
    (hi : BRefines s i (decIn w)) (hr : BRefines s r (decRegs w)) :
    Ensures s (body i r) (fun st t =>
      BRefines t st.out (fun e => outOf (decRegs w e)) ∧
      BRefines t st.next (fun e => stepOf (decIn w e) (decRegs w e)) ∧
      WritesOk t st.writes (ctx w).mems) := by
  obtain ⟨hev, hdr, hd, -⟩ := hi
  obtain ⟨hc0, ha0, hb0, hc1, ha1, hb1, hc2, ha2, hb2, -⟩ := hr
  unfold body
  rtl_let f0, hf0 ← flags_ensures hc0
  rtl_let f1, hf1 ← flags_ensures hc1
  rtl_let f2, hf2 ← flags_ensures hc2
  rtl_let n0, hn0 ← advance_ensures hw hf0 hev hf1.2.2.2.2 hd hc0 ha0 hb0
  obtain ⟨hn0a, hn0b, hn0c⟩ := hn0
  rtl_let n1, hn1 ← advance_ensures hw hf1 hf0.2.2.2.1 hf2.2.2.2.2 ha0 hc1 ha1 hb1
  obtain ⟨hn1a, hn1b, hn1c⟩ := hn1
  rtl_let n2, hn2 ← advance_ensures hw hf2 hf1.2.2.2.1 hdr ha1 hc2 ha2 hb2
  exact ensures_pure _ _ ⟨⟨hf0.2.2.2.2, hf0.2.2.2.1, ha0, hf1.2.2.2.2, hf1.2.2.2.1, ha1, hf2.2.2.2.2,
    hf2.2.2.2.1, ha2, trivial⟩, ⟨hn0a, hn0b, hn0c, hn1a, hn1b, hn1c, hn2.1, hn2.2.1, hn2.2.2, trivial⟩,
    WritesOk.nil⟩

def regsOf (w : Nat) (st : Store) : Regs w BitVec := Bundle.decode (Regs w) (st.regs.getD · 0)

theorem built (w : Nat) (hw : 0 < w) : ∃ (t : State (ctx w)) (sp : Step (Out w) (Regs w)),
    (design w).modules[(design w).top]? = some (t.toModule
      ⟨refs (Bundle.toVec sp.out), refs (Bundle.toVec sp.next), sp.writes⟩) ∧
    BRefines t sp.out (fun e => outOf (decRegs w e)) ∧
    BRefines t sp.next (fun e => stepOf (decIn w e) (decRegs w e)) ∧
    WritesOk t sp.writes (ctx w).mems := by
  obtain ⟨t, sp, hm, h⟩ := mealy_build (ctx_ok w hw) body _ _ (fun s i r hi hr => body_ensures w hw s i r hi hr)
  exact ⟨t, sp, congrArg some hm, h⟩

theorem moore (w : Nat) (hw : 0 < w) : (design w).IsMoore :=
  let ⟨_, _, hd, ho, _⟩ := built w hw
  mealy_isMoore hd ho (fun _ _ _ _ => rfl)

theorem design_step (w : Nat) (hw : 0 < w) (st : Store) (ins : Array Nat) (rst : Bool) :
    regsOf w ((design w).step st (ins, rst)) =
      Bundle.reset rst ⟨.sync 0, .none, .none, .sync 0, .none, .none, .sync 0, .none, .none⟩
        (stepOf (Bundle.decode (Fifo.Word.In w) (ins.getD · 0)) (regsOf w st)) ∧
    Bundle.decode (Out w) (((design w).output st ins).getD · 0) = outOf (regsOf w st) := by
  obtain ⟨t, sp, hd, ho, hn, -⟩ := built w hw
  exact ⟨mealy_step hd hn st (ins, rst), mealy_output hd ho st ins⟩

theorem stateBits (w : Nat) (hw : 0 < w) : Blast.stateBits (design w) (design w).top = 3 * (2 * w + 2) := by
  obtain ⟨t, sp, hd, -, -, hwr⟩ := built w hw
  rw [mealy_stateBits t sp hd hwr rfl]
  simp [Bundle.widths, Bundle.fields]
  omega

/-! ## Refinement of the queue network -/

/-- Each stage holds its queue. -/
def RegsHold (r : Regs w BitVec) (q : Fin 3 → List (BitVec w)) : Prop :=
  Holds r.count0 r.head0 r.tail0 (q 0) ∧ Holds r.count1 r.head1 r.tail1 (q 1) ∧
    Holds r.count2 r.head2 r.tail2 (q 2)

/-- A stage's flags and head word are its queue's outputs. -/
theorem port_holds {c : BitVec 2} {s0 s1 : BitVec w} {q : List (BitVec w)} (h : Holds c s0 s1 q) :
    (spec (BitVec w) 2).out q =
      ⟨(ready c).getLsbD 0, (valid c).getLsbD 0, if (valid c).getLsbD 0 then some s0 else none⟩ :=
  (flags_holds c s0 s1 q h).symm

/-- Data offered without valid does not matter. -/
theorem next_offer (q : List (BitVec w)) (v : Bool) (d f : BitVec w) (r : Bool) :
    (spec (BitVec w) 2).next q ⟨v, (if v then some d else none).getD f, r⟩ = (spec (BitVec w) 2).next q ⟨v, d, r⟩ := by
  cases v <;> simp [spec]

theorem step_holds (i : Fifo.Word.In w BitVec) (r : Regs w BitVec) (q : Fin 3 → List (BitVec w))
    (h : RegsHold r q) :
    RegsHold (stepOf i r) ((pipelineSpec (0 : BitVec w)).next q
      ⟨i.enqValid.getLsbD 0, i.data, i.deqReady.getLsbD 0⟩) := by
  obtain ⟨h0, h1, h2⟩ := h
  have o0 := port_holds h0
  have o1 := port_holds h1
  have o2 := port_holds h2
  refine ⟨?_, ?_, ?_⟩
  · show Holds _ _ _ ((spec (BitVec w) 2).next (q 0) ⟨i.enqValid.getLsbD 0, i.data,
      ((spec (BitVec w) 2).out (q 1)).enqReady⟩)
    rw [o1]
    exact advance_holds _ _ _ _ _ _ _ h0
  · show Holds _ _ _ ((spec (BitVec w) 2).next (q 1) ⟨((spec (BitVec w) 2).out (q 0)).deqValid,
      ((spec (BitVec w) 2).out (q 0)).deqData.getD 0, ((spec (BitVec w) 2).out (q 2)).enqReady⟩)
    rw [o0, o2]
    simp only
    rw [next_offer]
    exact advance_holds _ _ _ _ _ _ _ h1
  · show Holds _ _ _ ((spec (BitVec w) 2).next (q 2) ⟨((spec (BitVec w) 2).out (q 1)).deqValid,
      ((spec (BitVec w) 2).out (q 1)).deqData.getD 0, i.deqReady.getLsbD 0⟩)
    rw [o1]
    simp only
    rw [next_offer]
    exact advance_holds _ _ _ _ _ _ _ h2

theorem correct (w : Nat) (hw : 0 < w) :
    RefinesAfterReset ((design w).denote (moore w hw)) (wordSpec w) (observe w) 1 := by
  apply refinesAfterReset_of_simulation _ _ _ _ (fun st q => RegsHold (regsOf w st) q)
  · intro s₀ xs hr
    have h0 := hr 0 (by decide)
    show RegsHold (regsOf w ((design w).step s₀ ((xs 0).1, (xs 0).2))) _
    rw [(design_step w hw s₀ (xs 0).1 (xs 0).2).1, h0]
    generalize stepOf _ _ = r
    exact ⟨⟨show (bv 2 0).toNat ≤ 2 by decide, rfl⟩, ⟨show (bv 2 0).toNat ≤ 2 by decide, rfl⟩,
      ⟨show (bv 2 0).toNat ≤ 2 by decide, rfl⟩⟩
  · intro st q ins h
    show RegsHold (regsOf w ((design w).step st (ins, false))) _
    rw [(design_step w hw st ins false).1]
    exact step_holds _ _ q h
  · intro st q h
    funext k
    show observe w ((design w).output st #[]) k = (spec (BitVec w) 2).out (q k)
    obtain ⟨h0, h1, h2⟩ := h
    simp only [observe, (design_step w hw st #[] false).2]
    match k with
    | 0 => exact (port_holds h0).symm
    | 1 => exact (port_holds h1).symm
    | 2 => exact (port_holds h2).symm

end HDLean.SkidBuffer.Word
