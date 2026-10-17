import HDLean.Rtl.Mealy
import HDLean.Rtl.Tactic
import HDLean.Rtl.MealyDesign
import Designs.CounterRtl.Interface

/-!
# The decade counter in word-level RTL

One four-bit register with synchronous reset to zero, incremented when `en` is
set and wrapped from 9 to 0.
-/
namespace HDLean.Counter.Word
open HDLean.Rtl HDLean.Rtl.Build

hdl_record Regs where
  count : 4

def ctx : Ctx := Ctx.mealy "counter" In Out Regs ⟨.sync 0⟩ #[]

def body (i : In Sig) (r : Regs Sig) : M ctx (Step Out Regs) := do
  let nine ← const 4 9
  let one ← const 4 1
  let zero ← const 4 0
  let atNine ← eq r.count nine
  let inc ← add r.count one
  let wrapped ← mux atNine zero inc
  let nxt ← mux i.en wrapped r.count
  pure { out := ⟨r.count⟩, next := ⟨nxt⟩ }

def program : M ctx Wiring := mealy In Out Regs body

def design : Design := ⟨#[ctx.module program]⟩

/-! ## Proof -/

def decIn (e : Env) : In BitVec := Bundle.decode In (e.ins.getD · 0)
def decRegs (e : Env) : Regs BitVec := Bundle.decode Regs (e.st.regs.getD · 0)

/-- The next count, as the design computes it. -/
def stepCount (en : BitVec 1) (c : BitVec 4) : BitVec 4 :=
  if en.getLsbD 0 then (if c == 9 then 0 else c + 1) else c

theorem ctx_ok : ctx.ok = true := by decide

theorem body_ensures (s : State ctx) (i : In Sig) (r : Regs Sig)
    (hi : BRefines s i decIn) (hr : BRefines s r decRegs) :
    Ensures s (body i r) (fun st t =>
      BRefines t st.out (fun e => ⟨(decRegs e).count⟩) ∧
      BRefines t st.next (fun e => ⟨stepCount (decIn e).en (decRegs e).count⟩) ∧
      WritesOk t st.writes ctx.mems) := by
  obtain ⟨hen, -⟩ := hi
  obtain ⟨hc, -⟩ := hr
  unfold body
  rtl_let nine, hnine ← const_ensures _ 4 9 (by decide)
  rtl_let one, hone ← const_ensures _ 4 1 (by decide)
  rtl_let zero, hzero ← const_ensures _ 4 0 (by decide)
  rtl_let atNine, hat ← cmp_ensures .eq hc hnine
  rtl_let inc, hinc ← bin_ensures .add hc hone (by decide)
  rtl_let wrapped, hw ← mux_ensures hat hzero hinc (by decide)
  rtl_let nxt, hn ← mux_ensures hen hw hc (by decide)
  refine ensures_pure _ _ ⟨⟨hc, trivial⟩, ⟨⟨hn.1, fun e => ?_⟩, trivial⟩, WritesOk.nil⟩
  show State.val _ e nxt.ref = _
  rw [hn.2 e]
  congr 1
  show (if _ then _ else _) = stepCount (decIn e).en (decRegs e).count
  simp only [stepCount, CmpOp.eval, BinOp.eval, BitVec.getLsbD_ofBool]
  rfl

/-- The registers of a store, as a record. -/
def regsOf (st : Store) : Regs BitVec := Bundle.decode Regs (st.regs.getD · 0)

theorem built : ∃ (t : State ctx) (sp : Step Out Regs),
    design.modules[design.top]? = some (t.toModule
      ⟨refs (Bundle.toVec sp.out), refs (Bundle.toVec sp.next), sp.writes⟩) ∧
    BRefines t sp.out (fun e => ⟨(decRegs e).count⟩) ∧
    BRefines t sp.next (fun e => ⟨stepCount (decIn e).en (decRegs e).count⟩) ∧
    WritesOk t sp.writes ctx.mems := by
  obtain ⟨t, sp, hm, h⟩ := mealy_build ctx_ok body _ _ (fun s i r hi hr => body_ensures s i r hi hr)
  exact ⟨t, sp, congrArg some hm, h⟩

/-- The design never reads its inputs to compute its outputs. -/
theorem moore : design.IsMoore :=
  let ⟨_, _, hd, ho, _⟩ := built
  mealy_isMoore hd ho (fun _ _ _ _ => rfl)

theorem design_step (st : Store) (ins : Array Nat) (rst : Bool) :
    (regsOf (design.step st (ins, rst))).count =
      (if rst then 0 else stepCount (Bundle.decode In (ins.getD · 0)).en (regsOf st).count) ∧
    Bundle.decode Out ((design.output st ins).getD · 0) = ⟨(regsOf st).count⟩ := by
  obtain ⟨t, sp, hd, ho, hn, -⟩ := built
  refine ⟨?_, mealy_output hd ho st ins⟩
  rw [regsOf, mealy_step hd hn st (ins, rst)]
  cases rst <;> rfl

theorem stepCount_toNat (en : BitVec 1) (c : BitVec 4) (hc : c.toNat < 10) :
    (stepCount en c).toNat = spec.next c.toNat (en.getLsbD 0) ∧ (stepCount en c).toNat < 10 := by
  simp only [stepCount, spec]
  cases hen : en.getLsbD 0
  · simp [hc]
  · simp only [ite_true]
    by_cases h9 : c.toNat = 9
    · have : c = 9 := BitVec.eq_of_toNat_eq (by simpa using h9)
      subst this; decide
    · have hne : (c == 9) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h; apply h9; rw [h]; rfl
      rw [hne]
      have h1 : (1 : BitVec 4).toNat = 1 := rfl
      simp only [Bool.false_eq_true, ite_false, BitVec.toNat_add, h1]
      omega

theorem correct : RefinesAfterReset (design.denote moore) wordSpec value 1 := by
  apply refinesAfterReset_of_simulation _ _ _ _ (fun st n => (regsOf st).count.toNat = n ∧ n < 10)
  · intro s₀ xs hr
    have h0 := hr 0 (by decide)
    have := (design_step s₀ (xs 0).1 (xs 0).2).1
    simp only [h0, ite_true] at this
    exact ⟨by show (regsOf (design.step s₀ ((xs 0).1, (xs 0).2))).count.toNat = 0; rw [h0, this]; rfl, by decide⟩
  · intro st n ins ⟨hn, hlt⟩
    have hs := (design_step st ins false).1
    simp only [Bool.false_eq_true, ite_false] at hs
    have h := stepCount_toNat (Bundle.decode In (ins.getD · 0)).en (regsOf st).count (by rw [hn]; exact hlt)
    have he : wordSpec.next n ins = (stepCount (Bundle.decode In (ins.getD · 0)).en (regsOf st).count).toNat := by
      rw [h.1, hn]; rfl
    refine ⟨?_, by rw [he]; exact h.2⟩
    show (regsOf (design.step st (ins, false))).count.toNat = _
    rw [hs, he]
  · intro st n ⟨hn, _⟩
    show value (design.output st #[]) = n
    simp only [value, (design_step st #[] false).2]
    exact hn

/-- Four state bits: the count register. -/
theorem stateBits : Blast.stateBits design design.top = 4 := by
  obtain ⟨t, sp, hd, -, -, hw⟩ := built
  rw [mealy_stateBits t sp hd hw rfl]
  rfl

end HDLean.Counter.Word
