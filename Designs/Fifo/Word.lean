import HDLean.Rtl.MealyDesign
import HDLean.Rtl.Tactic
import Designs.Fifo.Interface

/-!
# The two-entry FIFO in word-level RTL

A two-bit occupancy count and two payload slots; `slot0` is the head. Ready and
valid are read from the count alone, so the design is a Moore machine.
-/
namespace HDLean.Fifo.Word
open HDLean.Rtl HDLean.Rtl.Build

/-! ## One two-entry stage, in any module

The stage is split in two so that stages can be chained through valid/ready
inside one module (`Designs.SkidBuffer.Word`): `flags` reads ready and valid off
the count; `advance` computes the next count and slots once every stage's flags
are known. -/

structure Flags where
  empty : Sig 1
  single : Sig 1
  full : Sig 1
  valid : Sig 1
  ready : Sig 1

def flags {c : Ctx} (count : Sig 2) : M c Flags := do
  let zero ← const 2 0
  let one ← const 2 1
  let two ← const 2 2
  let empty ← eq count zero
  let single ← eq count one
  let full ← eq count two
  let valid ← not empty
  let ready ← not full
  pure ⟨empty, single, full, valid, ready⟩

def advance {c : Ctx} (f : Flags) (enqValid deqReady : Sig 1) (data : Sig w) (count : Sig 2) (slot0 slot1 : Sig w) :
    M c (Sig 2 × Sig w × Sig w) := do
  let deq ← and deqReady f.valid
  let enq ← and enqValid f.ready
  let enq2 ← zext enq 2
  let deq2 ← zext deq 2
  let grown ← add count enq2
  let count' ← sub grown deq2
  let shifted ← mux f.single data slot1
  let kept ← mux f.empty data slot0
  let slot0' ← mux deq shifted kept
  let slot1' ← mux f.full slot1 data
  pure (count', slot0', slot1')

/-- The next count and slots, as `advance` computes them. -/
def advanceOf (ev dr : BitVec 1) (d : BitVec w) (c : BitVec 2) (s0 s1 : BitVec w) : BitVec 2 × BitVec w × BitVec w :=
  let deq := dr &&& ~~~(BitVec.ofBool (c == 0))
  let enq := ev &&& ~~~(BitVec.ofBool (c == 2))
  (c + enq.setWidth 2 - deq.setWidth 2,
   if deq.getLsbD 0 then (if (BitVec.ofBool (c == 1)).getLsbD 0 then d else s1)
   else (if (BitVec.ofBool (c == 0)).getLsbD 0 then d else s0),
   if (BitVec.ofBool (c == 2)).getLsbD 0 then s1 else d)

/-- The flags of a stage carry the comparisons of its count. -/
def FlagsRefine {c : Ctx} (t : State c) (f : Flags) (fc : Env → BitVec 2) : Prop :=
  Build.Refines t f.empty (fun e => BitVec.ofBool (fc e == 0)) ∧
  Build.Refines t f.single (fun e => BitVec.ofBool (fc e == 1)) ∧
  Build.Refines t f.full (fun e => BitVec.ofBool (fc e == 2)) ∧
  Build.Refines t f.valid (fun e => ~~~(BitVec.ofBool (fc e == 0))) ∧
  Build.Refines t f.ready (fun e => ~~~(BitVec.ofBool (fc e == 2)))

theorem FlagsRefine.mono {c : Ctx} {s t : State c} {f : Flags} {fc} (h : FlagsRefine s f fc) (hx : Extends s t) :
    FlagsRefine t f fc :=
  ⟨h.1.mono hx, h.2.1.mono hx, h.2.2.1.mono hx, h.2.2.2.1.mono hx, h.2.2.2.2.mono hx⟩

theorem flags_ensures {c : Ctx} {s : State c} {count : Sig 2} {fc} (hc : Build.Refines s count fc) :
    Ensures s (flags count) (fun f t => FlagsRefine t f fc) := by
  unfold flags
  rtl_let zero, hzero ← const_ensures _ 2 0 (by decide)
  rtl_let one, hone ← const_ensures _ 2 1 (by decide)
  rtl_let two, htwo ← const_ensures _ 2 2 (by decide)
  rtl_let empty, hempty ← cmp_ensures .eq hc hzero
  rtl_let single, hsingle ← cmp_ensures .eq hc hone
  rtl_let full, hfull ← cmp_ensures .eq hc htwo
  rtl_let valid, hvalid ← not_ensures hempty (by decide)
  rtl_let ready, hready ← not_ensures hfull (by decide)
  exact ensures_pure _ _ ⟨hempty, hsingle, hfull, hvalid, hready⟩

theorem advance_ensures {c : Ctx} {s : State c} {f : Flags} {ev dr : Sig 1} {d : Sig w} {count : Sig 2}
    {s0 s1 : Sig w} {fev fdr fd fc fs0 fs1} (hw : 0 < w) (hf : FlagsRefine s f fc) (hev : Build.Refines s ev fev)
    (hdr : Build.Refines s dr fdr) (hd : Build.Refines s d fd) (hc : Build.Refines s count fc) (hs0 : Build.Refines s s0 fs0)
    (hs1 : Build.Refines s s1 fs1) :
    Ensures s (advance f ev dr d count s0 s1) (fun r t =>
      Build.Refines t r.1 (fun e => (advanceOf (fev e) (fdr e) (fd e) (fc e) (fs0 e) (fs1 e)).1) ∧
      Build.Refines t r.2.1 (fun e => (advanceOf (fev e) (fdr e) (fd e) (fc e) (fs0 e) (fs1 e)).2.1) ∧
      Build.Refines t r.2.2 (fun e => (advanceOf (fev e) (fdr e) (fd e) (fc e) (fs0 e) (fs1 e)).2.2)) := by
  obtain ⟨hempty, hsingle, hfull, hvalid, hready⟩ := hf
  unfold advance
  rtl_let deq, hdeq ← bin_ensures .and hdr hvalid (by decide)
  rtl_let enq, henq ← bin_ensures .and hev hready (by decide)
  rtl_let enq2, henq2 ← zext_ensures 2 henq (by decide) (by decide)
  rtl_let deq2, hdeq2 ← zext_ensures 2 hdeq (by decide) (by decide)
  rtl_let grown, hgrown ← bin_ensures .add hc henq2 (by decide)
  rtl_let count', hcount ← bin_ensures .sub hgrown hdeq2 (by decide)
  rtl_let shifted, hshifted ← mux_ensures hsingle hd hs1 hw
  rtl_let kept, hkept ← mux_ensures hempty hd hs0 hw
  rtl_let slot0', hslot0 ← mux_ensures hdeq hshifted hkept hw
  rtl_let slot1', hslot1 ← mux_ensures hfull hs1 hd hw
  exact ensures_pure _ _ ⟨hcount, hslot0, hslot1⟩

/-! ## The two-entry FIFO -/

hdl_record Regs (w : Nat) where
  count : 2
  slot0 : w
  slot1 : w

def ctx (w : Nat) : Ctx := Ctx.mealy "fifo" (In w) (Out w) (Regs w) ⟨.sync 0, .none, .none⟩ #[]

def body (i : In w Sig) (r : Regs w Sig) : M (ctx w) (Step (Out w) (Regs w)) := do
  let f ← flags r.count
  let n ← advance f i.enqValid i.deqReady i.data r.count r.slot0 r.slot1
  pure { out := ⟨f.ready, f.valid, r.slot0⟩, next := ⟨n.1, n.2.1, n.2.2⟩ }

def program (w : Nat) : M (ctx w) Wiring := mealy (In w) (Out w) (Regs w) body

def design (w : Nat) : Design := ⟨#[(ctx w).module (program w)]⟩

/-! ## The design as functions of records -/

def decIn (w : Nat) (e : Env) : In w BitVec := Bundle.decode (In w) (e.ins.getD · 0)
def decRegs (w : Nat) (e : Env) : Regs w BitVec := Bundle.decode (Regs w) (e.st.regs.getD · 0)

/-- The outputs, as the design computes them. -/
def outOf (r : Regs w BitVec) : Out w BitVec :=
  ⟨~~~(BitVec.ofBool (r.count == 2)), ~~~(BitVec.ofBool (r.count == 0)), r.slot0⟩

/-- The next registers, as the design computes them. -/
def stepOf (i : In w BitVec) (r : Regs w BitVec) : Regs w BitVec :=
  let n := advanceOf i.enqValid i.deqReady i.data r.count r.slot0 r.slot1
  ⟨n.1, n.2.1, n.2.2⟩

theorem ctx_ok (w : Nat) (hw : 0 < w) : (ctx w).ok = true := by
  simp [Ctx.ok, ctx, Ctx.mealy, Bundle.ports, Bundle.fields, Bundle.toVec, HVec.toList, Reset.fits, hw]

theorem body_ensures (w : Nat) (hw : 0 < w) (s : State (ctx w)) (i : In w Sig) (r : Regs w Sig)
    (hi : BRefines s i (decIn w)) (hr : BRefines s r (decRegs w)) :
    Ensures s (body i r) (fun st t =>
      BRefines t st.out (fun e => outOf (decRegs w e)) ∧
      BRefines t st.next (fun e => stepOf (decIn w e) (decRegs w e)) ∧
      WritesOk t st.writes (ctx w).mems) := by
  obtain ⟨hev, hdr, hd, -⟩ := hi
  obtain ⟨hc, hs0, hs1, -⟩ := hr
  unfold body
  rtl_let f, hf ← flags_ensures hc
  rtl_let n, hn ← advance_ensures hw hf hev hdr hd hc hs0 hs1
  exact ensures_pure _ _ ⟨⟨hf.2.2.2.2, hf.2.2.2.1, hs0, trivial⟩, ⟨hn.1, hn.2.1, hn.2.2, trivial⟩, WritesOk.nil⟩

/-- The registers of a store, as a record. -/
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
      Bundle.reset rst ⟨.sync 0, .none, .none⟩ (stepOf (Bundle.decode (In w) (ins.getD · 0)) (regsOf w st)) ∧
    Bundle.decode (Out w) (((design w).output st ins).getD · 0) = outOf (regsOf w st) := by
  obtain ⟨t, sp, hd, ho, hn, -⟩ := built w hw
  exact ⟨mealy_step hd hn st (ins, rst), mealy_output hd ho st ins⟩

theorem stateBits (w : Nat) (hw : 0 < w) : Blast.stateBits (design w) (design w).top = 2 * w + 2 := by
  obtain ⟨t, sp, hd, -, -, hwr⟩ := built w hw
  rw [mealy_stateBits t sp hd hwr rfl]
  simp [Bundle.widths, Bundle.fields]
  omega

/-! ## Refinement of the bounded queue -/

/-- The queue a stage holds. -/
def contents (c : BitVec 2) (s0 s1 : BitVec w) : List (BitVec w) :=
  match c.toNat with
  | 0 => []
  | 1 => [s0]
  | _ => [s0, s1]

/-- What a stage must satisfy: at most two entries, holding the queue. -/
def Holds (c : BitVec 2) (s0 s1 : BitVec w) (q : List (BitVec w)) : Prop := c.toNat ≤ 2 ∧ contents c s0 s1 = q

theorem bit_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  have h := x.isLt
  rcases hx : x.toNat with _ | _ | n
  · exact .inl (BitVec.eq_of_toNat_eq hx)
  · exact .inr (BitVec.eq_of_toNat_eq hx)
  · omega

theorem count_cases (x : BitVec 2) (h : x.toNat ≤ 2) : x = 0#2 ∨ x = 1#2 ∨ x = 2#2 := by
  rcases hx : x.toNat with _ | _ | _ | n
  · exact .inl (BitVec.eq_of_toNat_eq hx)
  · exact .inr (.inl (BitVec.eq_of_toNat_eq hx))
  · exact .inr (.inr (BitVec.eq_of_toNat_eq hx))
  · omega

/-- One stage step is one step of the two-entry queue. -/
theorem advance_holds (ev dr : BitVec 1) (d : BitVec w) (c : BitVec 2) (s0 s1 : BitVec w) (q : List (BitVec w))
    (h : Holds c s0 s1 q) :
    let n := advanceOf ev dr d c s0 s1
    Holds n.1 n.2.1 n.2.2 ((spec (BitVec w) 2).next q ⟨ev.getLsbD 0, d, dr.getLsbD 0⟩) := by
  obtain ⟨hc, rfl⟩ := h
  rcases count_cases c hc with rfl | rfl | rfl <;> rcases bit_cases ev with rfl | rfl <;>
    rcases bit_cases dr with rfl | rfl <;> simp [advanceOf, contents, spec, Holds]

/-- A stage's ready, valid and head word are the queue's outputs. -/
theorem flags_holds (c : BitVec 2) (s0 s1 : BitVec w) (q : List (BitVec w)) (h : Holds c s0 s1 q) :
    (⟨(~~~(BitVec.ofBool (c == 2))).getLsbD 0, (~~~(BitVec.ofBool (c == 0))).getLsbD 0,
      if (~~~(BitVec.ofBool (c == 0))).getLsbD 0 then some s0 else none⟩ : Output (BitVec w)) =
      (spec (BitVec w) 2).out q := by
  obtain ⟨hc, rfl⟩ := h
  rcases count_cases c hc with rfl | rfl | rfl <;> simp [contents, spec]

/-- What the registers must satisfy. -/
def RegsHold (r : Regs w BitVec) (q : List (BitVec w)) : Prop := Holds r.count r.slot0 r.slot1 q

theorem correct (w : Nat) (hw : 0 < w) :
    RefinesAfterReset ((design w).denote (moore w hw)) (queueSpec 2 w) (observe w) 1 := by
  apply refinesAfterReset_of_simulation _ _ _ _ (fun st q => RegsHold (regsOf w st) q)
  · intro s₀ xs hr
    have h0 := hr 0 (by decide)
    show RegsHold (regsOf w ((design w).step s₀ ((xs 0).1, (xs 0).2))) []
    rw [(design_step w hw s₀ (xs 0).1 (xs 0).2).1, h0]
    generalize stepOf _ _ = r
    exact ⟨show (bv 2 0).toNat ≤ 2 by decide, rfl⟩
  · intro st q ins h
    show RegsHold (regsOf w ((design w).step st (ins, false))) _
    rw [(design_step w hw st ins false).1]
    exact advance_holds _ _ _ _ _ _ q h
  · intro st q h
    show observe w ((design w).output st #[]) = _
    simp only [observe, (design_step w hw st #[] false).2]
    exact flags_holds _ _ _ q h

end HDLean.Fifo.Word
