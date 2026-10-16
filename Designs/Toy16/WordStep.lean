import Designs.Toy16.WordBody

/-! # One cycle of the Toy16 design, stated over words -/
namespace HDLean.Toy16.Word
open HDLean.Rtl HDLean.Rtl.Build

def regsOfStore (st : Store) : CpuRegs BitVec := Bundle.decode CpuRegs (st.regs.getD · 0)
def instrOfIns (ins : Array Nat) : Word := (Bundle.decode CpuIn (ins.getD · 0)).instr

theorem top_eq : design.modules[design.top]? = some cpuModule := rfl

theorem aluOf_eq (k : Nat) (st : Store) (ins : Array Nat) (rst : Bool) :
    aluOf k ⟨design.env design.top, st, ins, rst⟩ =
      aluHw (Hw.opc (instrOfIns ins)) (Hw.a (instrOfIns ins) (st.mem 0 3 16)) (Hw.bsel (instrOfIns ins) (st.mem 0 3 16)) := by
  unfold aluOf
  dsimp only
  have henv : design.env design.top 0 = design.sem 0 := Design.env_lt _ (by decide)
  rw [henv, Design.sem_eq design 0 aluModule rfl]
  have h := congrArg AluOut.y (alu_output (design.env 0) ((st.subs.getD k default))
    #[(Hw.opc (instrOfIns ins)).toNat, (Hw.a (instrOfIns ins) (st.mem 0 3 16)).toNat,
      (Hw.bsel (instrOfIns ins) (st.mem 0 3 16)).toNat] rst)
  simp only [Bundle.decode, Bundle.ofVec, Bundle.widths, Bundle.fields, List.map, HVec.decode, HVec.head,
    HVec.tail] at h
  simp only [unpack, HVec.decode, HVec.head, ← getD_toList]
  refine h.trans ?_
  simp

theorem cpu_built : ∃ (t : State cpuCtx) (sp : Step CpuOut CpuRegs) (k : Nat),
    cpuModule = t.toModule ⟨refs (Bundle.toVec sp.out), refs (Bundle.toVec sp.next), sp.writes⟩ ∧
    BRefines t sp.out (fun e => Hw.out (regsOf e)) ∧
    BRefines t sp.next (fun e => Hw.next (instrOf e) (regsOf e) (rfOf e) (dmOf e) (aluOf k e)) ∧
    WritesOk t sp.writes cpuMems ∧
    ∃ p q, sp.writes = #[#[p], #[q]] ∧ PortsRefine t [p] [rfWrite k] ∧ PortsRefine t [q] [dmWrite] :=
  mealy_build_ex cpuCtx_ok cpuBody (fun _ e => Hw.out (regsOf e))
    (fun k e => Hw.next (instrOf e) (regsOf e) (rfOf e) (dmOf e) (aluOf k e))
    (fun k sp t => ∃ p q, sp.writes = #[#[p], #[q]] ∧ PortsRefine t [p] [rfWrite k] ∧ PortsRefine t [q] [dmWrite])
    (fun s i r hi hr => cpuBody_ensures s i r hi hr)

section
variable (st : Store) (ins : Array Nat) (rst : Bool)

/-- What the ALU instance returns in this cycle. -/
def aluNow : Word := aluHw (Hw.opc (instrOfIns ins)) (Hw.a (instrOfIns ins) (st.mem 0 3 16))
  (Hw.bsel (instrOfIns ins) (st.mem 0 3 16))

/-- Next registers. -/
theorem step_regs : regsOfStore (design.step st (ins, rst)) = Bundle.reset rst resets
    (Hw.next (instrOfIns ins) (regsOfStore st) (st.mem 0 3 16) (st.mem 1 8 16) (aluNow st ins)) := by
  obtain ⟨t, sp, k, hm, -, hn, -⟩ := cpu_built
  rw [Design.step_eq _ _ top_eq, hm]
  refine (mealy_regs t sp _ hn (design.env design.top) st ins rst).trans ?_
  show Bundle.reset rst resets (Hw.next _ _ _ _ (aluOf k ⟨design.env design.top, st, ins, rst⟩)) = _
  rw [aluOf_eq]
  rfl

/-- The register file after the cycle. -/
theorem step_rf (a : BitVec 3) : (design.step st (ins, rst)).mem 0 3 16 a =
    if (Hw.live (regsOfStore st) &&& Hw.wbe (instrOfIns ins)).getLsbD 0 = true ∧ Hw.rd (instrOfIns ins) = a then
      Hw.wbd (instrOfIns ins) (st.mem 0 3 16) (st.mem 1 8 16) (aluNow st ins)
    else st.mem 0 3 16 a := by
  obtain ⟨t, sp, k, hm, -, -, -, p, q, hw, hp, -⟩ := cpu_built
  rw [Design.step_eq _ _ top_eq, hm]
  refine (mealy_mem t sp 0 ⟨"rf", 3, 16, 1⟩ #[p] [rfWrite k] rfl (by rw [hw]; rfl) hp
    (design.env design.top) st ins rst a).trans ?_
  simp only [WriteSpec.apply, List.foldl_cons, List.foldl_nil, rfWrite]
  rw [aluOf_eq]
  rfl

/-- The data memory after the cycle. -/
theorem step_dm (a : Addr) : (design.step st (ins, rst)).mem 1 8 16 a =
    if (Hw.live (regsOfStore st) &&& Hw.isOp (instrOfIns ins) 8).getLsbD 0 = true ∧
        Hw.ea (instrOfIns ins) (st.mem 0 3 16) = a then
      Hw.v (instrOfIns ins) (st.mem 0 3 16)
    else st.mem 1 8 16 a := by
  obtain ⟨t, sp, k, hm, -, -, -, p, q, hw, -, hq⟩ := cpu_built
  rw [Design.step_eq _ _ top_eq, hm]
  exact mealy_mem t sp 1 ⟨"dmem", 8, 16, 1⟩ #[q] [dmWrite] rfl (by rw [hw]; rfl) hq
    (design.env design.top) st ins rst a

/-- The outputs, which depend on the registers only. -/
theorem output_eq : Bundle.decode CpuOut ((design.output st ins).getD · 0) = Hw.out (regsOfStore st) := by
  obtain ⟨t, sp, k, hm, ho, -⟩ := cpu_built
  rw [Design.output_eq _ _ top_eq, hm]
  exact mealy_outputs t sp _ ho (design.env design.top) st ins false

end

end HDLean.Toy16.Word
