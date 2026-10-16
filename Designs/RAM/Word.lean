import HDLean.Rtl.Memory
import Designs.RAMRtl.Interface

/-!
# A single-port RAM on the memory primitive

`2^a` words of `w` bits held in one RTL memory (not in flip-flops), one write
port, and a registered read word. The proof uses the memory read and write
lemmas only; no bit is mentioned.
-/
namespace HDLean.RAM.Word
open HDLean.Rtl HDLean.Rtl.Build

hdl_record Regs (w : Nat) where
  rd : w

def ctx (a w : Nat) : Ctx := Ctx.mealy "ram" (In a w) (Out w) (Regs w) ⟨.none⟩ #[⟨"cells", a, w, 1⟩]

def body (i : In a w Sig) (r : Regs w Sig) : M (ctx a w) (Step (Out w) (Regs w)) := do
  let x ← memRead 0 w i.addr
  pure { out := ⟨r.rd⟩, next := ⟨x⟩, writes := #[#[port i.we i.addr i.wdata]] }

def program (a w : Nat) : M (ctx a w) Wiring := mealy (In a w) (Out w) (Regs w) body

def design (a w : Nat) : Design := ⟨#[(ctx a w).module (program a w)]⟩

/-! ## Specification view -/

def decIn (a w : Nat) (e : Env) : In a w BitVec := Bundle.decode (In a w) (e.ins.getD · 0)
def decRegs (w : Nat) (e : Env) : Regs w BitVec := Bundle.decode (Regs w) (e.st.regs.getD · 0)

/-- The store as the reference RAM state: memory 0 and register 0. -/
def decode (a w : Nat) (st : Store) : RAMState (2 ^ a) w :=
  ⟨Vector.ofFn fun i => st.mem 0 a w (BitVec.ofFin i), bv w (st.regs.getD 0 0)⟩

/-- The write port: enable, address and data straight from the inputs. -/
def writeSpec (a w : Nat) : WriteSpec a w :=
  ⟨fun e => (decIn a w e).we.getLsbD 0, fun e => (decIn a w e).addr, fun e => (decIn a w e).wdata⟩

theorem ram_cell (i : In a w BitVec) (m : BitVec a → BitVec w) (r : BitVec w) (k : Nat) (hk : k < 2 ^ a) :
    ((ram (2 ^ a) w).next ⟨Vector.ofFn (fun j => m (BitVec.ofFin j)), r⟩
      ⟨i.addr.toFin, if i.we.getLsbD 0 then some i.wdata else none⟩).cells[k] =
      if i.we.getLsbD 0 = true ∧ i.addr = BitVec.ofFin ⟨k, hk⟩ then i.wdata else m (BitVec.ofFin ⟨k, hk⟩) := by
  simp only [ram]
  have key : (i.addr = BitVec.ofFin ⟨k, hk⟩) ↔ i.addr.toNat = k :=
    ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩
  simp only [key]
  cases hwe : i.we.getLsbD 0 <;> by_cases hk' : i.addr.toNat = k <;> simp [hk', Vector.getElem_set]

theorem ctx_ok (a w : Nat) (ha : 0 < a) (hw : 0 < w) : (ctx a w).ok = true := by
  simp [Ctx.ok, ctx, Ctx.mealy, Bundle.ports, Bundle.fields, Bundle.toVec, HVec.toList, Reset.fits, ha, hw]

theorem body_ensures (a w : Nat) (hw : 0 < w) (s : State (ctx a w)) (i : In a w Sig) (r : Regs w Sig)
    (hi : BRefines s i (decIn a w)) (hr : BRefines s r (decRegs w)) :
    Ensures s (body i r) (fun st t =>
      BRefines t st.out (fun e => ⟨(decRegs w e).rd⟩) ∧
      BRefines t st.next (fun e => ⟨e.st.mem 0 a w (decIn a w e).addr⟩) ∧
      WritesOk t st.writes (ctx a w).mems ∧
      ∃ ps, st.writes = #[ps] ∧ PortsRefine t ps.toList [writeSpec a w]) := by
  obtain ⟨hwe, haddr, hdata, -⟩ := hi
  obtain ⟨hrd, -⟩ := hr
  unfold body
  rtl_let x, hx ← memRead_ensures 0 w haddr hw (by simp [ctx])
  refine ensures_pure _ _ ⟨⟨hrd, trivial⟩, ⟨⟨hx.1, fun e => hx.2 e⟩, trivial⟩, ?_, _, rfl,
    .cons (port_refines hwe haddr hdata) .nil⟩
  · refine ⟨rfl, fun j ps m h1 h2 => ?_⟩
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
    exact ⟨hwe.1, haddr.1, hdata.1⟩

/-- One cycle of the RAM design is one step of the reference RAM, whatever the
reset input (the RAM has no reset), for every store. -/
theorem design_step (a w : Nat) (ha : 0 < a) (hw : 0 < w) (st : Store) (ins : Array Nat) (rst : Bool) :
    decode a w ((design a w).step st (ins, rst)) = (ram (2 ^ a) w).next (decode a w st) (request a w ins) ∧
    bv w (((design a w).output st ins).getD 0 0) = (ram (2 ^ a) w).out (decode a w st) := by
  obtain ⟨t, sp, hm, ho, hn, -, ps, hwr, hps⟩ := mealy_build_with (ctx_ok a w ha hw) body _ _ _
    (fun s i r hi hr => body_ensures a w hw s i r hi hr)
  have htop : (design a w).modules[(design a w).top]? = some ((ctx a w).module (program a w)) := rfl
  constructor
  · rw [Design.step_eq _ _ htop]
    have hm' : (ctx a w).module (program a w) = _ := hm
    rw [hm']
    have hregs := mealy_regs t sp _ hn ((design a w).env (design a w).top) st ins rst
    have hmem := mealy_mem t sp 0 ⟨"cells", a, w, 1⟩ _ _ rfl (by rw [hwr]; rfl) hps
      ((design a w).env (design a w).top) st ins rst
    unfold decode
    congr 1
    · apply Vector.ext
      intro k hk
      rw [Vector.getElem_ofFn, hmem]
      simp only [WriteSpec.apply, List.foldl_cons, List.foldl_nil, writeSpec, decIn, request]
      exact (ram_cell _ _ (bv w (st.regs.getD 0 0)) k hk).symm
    · have := congrArg (fun r : Regs w BitVec => r.rd) hregs
      simp only [Bundle.reset, Bundle.decode, Bundle.toVec, Bundle.ofVec, HVec.zipWith, resetField, Bundle.widths,
        Bundle.fields, List.map, HVec.decode, HVec.head] at this
      simp only [Bundle.toVec, request, decIn, Vector.getElem_ofFn]
      rw [this]
      simp [decIn, Store.mem]
  · rw [Design.output_eq _ _ htop]
    have hm' : (ctx a w).module (program a w) = _ := hm
    rw [hm']
    have := congrArg (fun r : Out w BitVec => r.rdata)
      (mealy_outputs t sp _ ho ((design a w).env (design a w).top) st ins false)
    simp only [Bundle.decode, Bundle.toVec, Bundle.ofVec, Bundle.widths, Bundle.fields, List.map, HVec.decode,
      HVec.head] at this
    simp only [Bundle.toVec]
    rw [this]
    rfl

/-- From any power-up store and under any input sequence (reset included, which
the RAM ignores), the decoded state follows the reference RAM cycle for cycle,
and the read port shows the reference read word. -/
theorem correctness (a w : Nat) (ha : 0 < a) (hw : 0 < w) (s₀ : Store) (xs : Nat → Array Nat × Bool) (t : Nat) :
    decode a w ((machine (design a w)).stateFrom s₀ xs t) = (ram (2 ^ a) w).stateFrom (decode a w s₀) (fun n => request a w (xs n).1) t ∧
    ∀ ins, bv w (((design a w).output ((machine (design a w)).stateFrom s₀ xs t) ins).getD 0 0) =
      (ram (2 ^ a) w).runFrom (decode a w s₀) (fun n => request a w (xs n).1) t := by
  have hs : ∀ t, decode a w ((machine (design a w)).stateFrom s₀ xs t) =
      (ram (2 ^ a) w).stateFrom (decode a w s₀) (fun n => request a w (xs n).1) t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [PMachine.stateFrom_succ]
      rw [← ih]
      exact (design_step a w ha hw _ (xs t).1 (xs t).2).1
  refine ⟨hs t, fun ins => ?_⟩
  rw [(design_step a w ha hw _ ins false).2, hs t]
  rfl

theorem correctness_impl (a w : Nat) (ha : 0 < a) (hw : 0 < w) (s₀ : Store) (xs : Nat → Array Nat × Bool) :
    ∃ m₀ : RAMState (2 ^ a) w, ∀ t, readWord w (design a w) ((machine (design a w)).stateFrom s₀ xs t) =
      (ram (2 ^ a) w).runFrom m₀ (fun n => request a w (xs n).1) t :=
  ⟨decode a w s₀, fun t => (correctness a w ha hw s₀ xs t).2 #[]⟩

end HDLean.RAM.Word
