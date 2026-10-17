import HDLean.Rtl.MealyDesign
import HDLean.Rtl.Tactic
import Designs.Fifo.Interface
import Designs.Fifo.CircularQueue

/-!
# The general-depth FIFO in word-level RTL

`2^k` payload words in one RTL memory (not flip-flops), a `k`-bit head pointer
and a `k+1`-bit occupancy count. The design implements the circular-buffer
model `Fifo.Circular.machine` cycle for cycle; that model's refinement of the
bounded queue (`Fifo.Circular.trace_refines_queue`) does the rest.
-/
namespace HDLean.Fifo.Circular.Word
open HDLean.Rtl HDLean.Rtl.Build HDLean.Fifo HDLean.Fifo.Word

hdl_record Regs (k : Nat) where
  head : k
  count : (k + 1)

def ctx (k w : Nat) : Ctx :=
  Ctx.mealy "circular_fifo" (In w) (Out w) (Regs k) ⟨.sync 0, .sync 0⟩ #[⟨"buffer", k, w, 1⟩]

def body (i : In w Sig) (r : Regs k Sig) : M (ctx k w) (Step (Out w) (Regs k)) := do
  let cap ← const (k + 1) (BitVec.ofNat (k + 1) (2 ^ k))
  let zero ← const (k + 1) 0
  let one ← const k 1
  let ready ← ult r.count cap
  let valid ← ne r.count zero
  let enq ← and i.enqValid ready
  let deq ← and i.deqReady valid
  let used ← slice r.count 0 k
  let tail ← add r.head used
  let advanced ← add r.head one
  let head ← mux deq advanced r.head
  let enqW ← zext enq (k + 1)
  let deqW ← zext deq (k + 1)
  let grown ← add r.count enqW
  let count ← sub grown deqW
  let word ← memRead 0 w r.head
  pure { out := ⟨ready, valid, word⟩, next := ⟨head, count⟩, writes := #[#[port enq tail i.data]] }

def program (k w : Nat) : M (ctx k w) Wiring := mealy (In w) (Out w) (Regs k) body

def design (k w : Nat) : Design := ⟨#[(ctx k w).module (program k w)]⟩

/-! ## The design as functions of records -/

def decIn (w : Nat) (e : Env) : In w BitVec := Bundle.decode (In w) (e.ins.getD · 0)
def decRegs (k : Nat) (e : Env) : Regs k BitVec := Bundle.decode (Regs k) (e.st.regs.getD · 0)

def readyOf (c : BitVec (k + 1)) : BitVec 1 := BitVec.ofBool (CmpOp.ult.eval c (BitVec.ofNat (k + 1) (2 ^ k)))
def validOf (c : BitVec (k + 1)) : BitVec 1 := BitVec.ofBool (CmpOp.ne.eval c 0)

def outOf (r : Regs k BitVec) (m : BitVec k → BitVec w) : Out w BitVec :=
  ⟨readyOf r.count, validOf r.count, m r.head⟩

def enqOf (i : In w BitVec) (r : Regs k BitVec) : BitVec 1 := i.enqValid &&& readyOf r.count
def deqOf (i : In w BitVec) (r : Regs k BitVec) : BitVec 1 := i.deqReady &&& validOf r.count

def stepOf (i : In w BitVec) (r : Regs k BitVec) : Regs k BitVec :=
  ⟨if (deqOf i r).getLsbD 0 then r.head + 1 else r.head,
   r.count + (enqOf i r).setWidth (k + 1) - (deqOf i r).setWidth (k + 1)⟩

def writeSpec (k w : Nat) : WriteSpec k w :=
  ⟨fun e => (enqOf (decIn w e) (decRegs k e)).getLsbD 0,
   fun e => (decRegs k e).head + (decRegs k e).count.extractLsb' 0 k, fun e => (decIn w e).data⟩

theorem ctx_ok (k w : Nat) (hk : 0 < k) (hw : 0 < w) : (ctx k w).ok = true := by
  simp [Ctx.ok, ctx, Ctx.mealy, Bundle.ports, Bundle.fields, Bundle.toVec, HVec.toList, Reset.fits, hk, hw, Nat.two_pow_pos]

theorem body_ensures (k w : Nat) (hk : 0 < k) (hw : 0 < w) (s : Build.State (ctx k w)) (i : In w Sig) (r : Regs k Sig)
    (hi : BRefines s i (decIn w)) (hr : BRefines s r (decRegs k)) :
    Ensures s (body i r) (fun st t =>
      BRefines t st.out (fun e => outOf (decRegs k e) (e.st.mem 0 k w)) ∧
      BRefines t st.next (fun e => stepOf (decIn w e) (decRegs k e)) ∧
      WritesOk t st.writes (ctx k w).mems ∧
      ∃ ps, st.writes = #[ps] ∧ PortsRefine t ps.toList [writeSpec k w]) := by
  obtain ⟨hev, hdr, hd, -⟩ := hi
  obtain ⟨hh, hc, -⟩ := hr
  unfold body
  rtl_let cap, hcap ← const_ensures _ (k + 1) (BitVec.ofNat (k + 1) (2 ^ k)) (by omega)
  rtl_let zero, hzero ← const_ensures _ (k + 1) 0 (by omega)
  rtl_let one, hone ← const_ensures _ k 1 hk
  rtl_let ready, hready ← cmp_ensures .ult hc hcap
  rtl_let valid, hvalid ← cmp_ensures .ne hc hzero
  rtl_let enq, henq ← bin_ensures .and hev hready (by decide)
  rtl_let deq, hdeq ← bin_ensures .and hdr hvalid (by decide)
  rtl_let used, hused ← slice_ensures 0 k hc hk (by omega)
  rtl_let tail, htail ← bin_ensures .add hh hused hk
  rtl_let advanced, hadv ← bin_ensures .add hh hone hk
  rtl_let head, hhead ← mux_ensures hdeq hadv hh hk
  rtl_let enqW, henqW ← zext_ensures (k + 1) henq (by omega) (by omega)
  rtl_let deqW, hdeqW ← zext_ensures (k + 1) hdeq (by omega) (by omega)
  rtl_let grown, hgrown ← bin_ensures .add hc henqW (by omega)
  rtl_let count, hcount ← bin_ensures .sub hgrown hdeqW (by omega)
  rtl_let word, hword ← memRead_ensures 0 w hh hw (by simp [ctx])
  refine ensures_pure _ _ ⟨⟨hready, hvalid, hword, trivial⟩, ⟨hhead, hcount, trivial⟩, ?_, _, rfl,
    .cons (port_refines henq htail hd) .nil⟩
  refine ⟨rfl, fun j ps m h1 h2 => ?_⟩
  have hj : j = 0 := by
    rcases j with _ | j
    · rfl
    · simp at h1
  subst hj
  simp [ctx] at h1 h2
  subst h1; subst h2
  refine ⟨rfl, fun p hp => ?_⟩
  simp at hp
  subst hp
  exact ⟨henq.1, htail.1, hd.1⟩

def regsOf (k : Nat) (st : Store) : Regs k BitVec := Bundle.decode (Regs k) (st.regs.getD · 0)

theorem built (k w : Nat) (hk : 0 < k) (hw : 0 < w) : ∃ (t : Build.State (ctx k w)) (sp : Step (Out w) (Regs k)),
    (design k w).modules[(design k w).top]? = some (t.toModule
      ⟨refs (Bundle.toVec sp.out), refs (Bundle.toVec sp.next), sp.writes⟩) ∧
    BRefines t sp.out (fun e => outOf (decRegs k e) (e.st.mem 0 k w)) ∧
    BRefines t sp.next (fun e => stepOf (decIn w e) (decRegs k e)) ∧
    WritesOk t sp.writes (ctx k w).mems ∧
    ∃ ps, sp.writes = #[ps] ∧ PortsRefine t ps.toList [writeSpec k w] := by
  obtain ⟨t, sp, hm, h⟩ := mealy_build_with (ctx_ok k w hk hw) body _ _ _
    (fun s i r hi hr => body_ensures k w hk hw s i r hi hr)
  exact ⟨t, sp, congrArg some hm, h⟩

theorem moore (k w : Nat) (hk : 0 < k) (hw : 0 < w) : (design k w).IsMoore :=
  let ⟨_, _, hd, ho, _⟩ := built k w hk hw
  mealy_isMoore hd ho (fun _ _ _ _ => rfl)

theorem stateBits (k w : Nat) (hk : 0 < k) (hw : 0 < w) :
    Blast.stateBits (design k w) (design k w).top = 2 * k + 1 + 2 ^ k * w := by
  obtain ⟨t, sp, hd, -, -, hwr, -⟩ := built k w hk hw
  rw [mealy_stateBits t sp hd hwr rfl]
  simp [Bundle.widths, Bundle.fields]
  omega

/-! ## The design is the circular-buffer model -/

/-- The store as a model state: memory 0 and the two registers. -/
def decode (k w : Nat) (st : Store) : Circular.State w k :=
  ⟨st.mem 0 k w, (regsOf k st).head, (regsOf k st).count⟩

theorem setWidth_bit (x : BitVec 1) (n : Nat) (hn : 0 < n) :
    x.setWidth n = if x.getLsbD 0 then 1#n else 0#n := by
  have h := x.isLt
  rcases hx : x.toNat with _ | _ | m
  · have : x = 0#1 := BitVec.eq_of_toNat_eq hx
    subst this; simp
  · have : x = 1#1 := BitVec.eq_of_toNat_eq hx
    subst this
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, Nat.one_mod_two_pow hn]
  · omega

theorem ready_bit (c : BitVec (k + 1)) : (readyOf c).getLsbD 0 = decide (c.toNat < 2 ^ k) := by
  have h : (2 ^ k) % 2 ^ (k + 1) = 2 ^ k := Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  simp [readyOf, CmpOp.eval, BitVec.ult, h]

theorem valid_bit (c : BitVec (k + 1)) : (validOf c).getLsbD 0 = (c != 0) := by
  simp [validOf, CmpOp.eval]

theorem extract_setWidth (c : BitVec (k + 1)) : c.extractLsb' 0 k = c.setWidth k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb', BitVec.toNat_setWidth]

theorem step_regs (k w : Nat) (hk : 0 < k) (i : In w BitVec) (r : Regs k BitVec) :
    stepOf i r = ⟨((machine w k).next ⟨fun _ => 0, r.head, r.count⟩ (⟨i.enqValid.getLsbD 0, i.data, i.deqReady.getLsbD 0⟩, false)).head,
      ((machine w k).next ⟨fun _ => 0, r.head, r.count⟩ (⟨i.enqValid.getLsbD 0, i.data, i.deqReady.getLsbD 0⟩, false)).count⟩ := by
  simp only [stepOf, machine, enqOf, deqOf, BitVec.getLsbD_and, ready_bit, valid_bit,
    setWidth_bit _ (k + 1) (by omega), Bool.false_eq_true, ite_false]
  congr 1 <;> split <;> split <;> simp_all

theorem decode_step (k w : Nat) (hk : 0 < k) (hw : 0 < w) (st : Store) (ins : Array Nat) :
    decode k w ((design k w).step st (ins, false)) = (machine w k).next (decode k w st) (decodeInput w ins, false) := by
  obtain ⟨t, sp, hd, -, hn, -, ps, hwr, hps⟩ := built k w hk hw
  have hr : regsOf k ((design k w).step st (ins, false)) = _ := mealy_step hd hn st (ins, false)
  have hm := fun a => mealy_step_mem hd 0 ⟨"buffer", k, w, 1⟩ ps [writeSpec k w] rfl (by rw [hwr]; rfl) hps
    st (ins, false) a
  have hs := step_regs k w hk (Bundle.decode (In w) (ins.getD · 0)) (regsOf k st)
  have hr' : regsOf k ((design k w).step st (ins, false)) =
      stepOf (Bundle.decode (In w) (ins.getD · 0)) (regsOf k st) := by rw [hr]; rfl
  unfold decode
  rw [hr', hs]
  simp only [machine, Bool.false_eq_true, ite_false, decodeInput]
  congr 1
  funext a
  rw [hm a]
  simp only [WriteSpec.apply, List.foldl_cons, List.foldl_nil, writeSpec, enqOf, decIn, decRegs,
    BitVec.getLsbD_and, ready_bit, extract_setWidth]
  simp only [regsOf, Bool.and_eq_true, beq_iff_eq, eq_comm (a := a)]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem decode_reset (k w : Nat) (hk : 0 < k) (hw : 0 < w) (st : Store) (ins : Array Nat) :
    (decode k w ((design k w).step st (ins, true))).head = 0 ∧
      (decode k w ((design k w).step st (ins, true))).count = 0 := by
  obtain ⟨t, sp, hd, -, hn, -⟩ := built k w hk hw
  have hr : regsOf k ((design k w).step st (ins, true)) = _ := mealy_step hd hn st (ins, true)
  unfold decode
  rw [hr]
  exact ⟨by simp [Bundle.reset, Bundle.toVec, Bundle.ofVec, HVec.zipWith, resetField],
    by simp [Bundle.reset, Bundle.toVec, Bundle.ofVec, HVec.zipWith, resetField]⟩

theorem decode_out (k w : Nat) (hk : 0 < k) (hw : 0 < w) (st : Store) :
    observe w ((design k w).output st #[]) = (machine w k).out (decode k w st) := by
  obtain ⟨t, sp, hd, ho, -⟩ := built k w hk hw
  simp only [observe, mealy_output hd ho st #[], outOf, ready_bit, valid_bit, machine, decode, regsOf, decRegs]

theorem correct (k w : Nat) (hk : 0 < k) (hw : 0 < w) :
    RefinesAfterReset ((design k w).denote (moore k w hk hw)) (queueSpec (2 ^ k) w) (observe w) 1 := by
  apply refinesAfterReset_of_simulation _ _ _ _ (fun st q => QueueRelation (decode k w st) q)
  · intro s₀ xs hr
    obtain ⟨hh, hc⟩ := decode_reset k w hk hw s₀ (xs 0).1
    show QueueRelation (decode k w ((design k w).step s₀ (xs 0))) []
    have hx : xs 0 = ((xs 0).1, true) := Prod.ext rfl (hr 0 (by decide))
    rw [hx]
    refine ⟨⟨0, 0⟩, fun _ => 0, by simp [Ghost.Safe], ⟨by rw [hh]; rfl, by rw [hc]; rfl⟩,
      fun n _ h2 => absurd h2 (Nat.not_lt_zero n), by simp [queue]⟩
  · intro st q ins h
    show QueueRelation (decode k w ((design k w).step st (ins, false))) _
    rw [decode_step k w hk hw]
    exact queue_relation_step h _
  · intro st q h
    show observe w ((design k w).output st #[]) = (spec (BitVec w) (2 ^ k)).out q
    rw [← queue_relation_out h]
    exact decode_out k w hk hw st

end HDLean.Fifo.Circular.Word
