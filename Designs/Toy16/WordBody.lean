import Designs.Toy16.WordCore

/-! # The built core computes `Hw.next`, `Hw.out` and the two write ports -/
namespace HDLean.Toy16.Word
open HDLean.Rtl HDLean.Rtl.Build

set_option maxHeartbeats 1000000 in
theorem cpuBody_ensures (s : State cpuCtx) (i : CpuIn Sig) (r : CpuRegs Sig)
    (hi : BRefines s i (fun e => Bundle.decode CpuIn (e.ins.getD · 0)))
    (hr : BRefines s r regsOf) :
    Ensures s (cpuBody i r) (fun st t => ∃ k,
      BRefines t st.out (fun e => Hw.out (regsOf e)) ∧
      BRefines t st.next (fun e => Hw.next (instrOf e) (regsOf e) (rfOf e) (dmOf e) (aluOf k e)) ∧
      WritesOk t st.writes cpuCtx.mems ∧
      ∃ p q, st.writes = #[#[p], #[q]] ∧ PortsRefine t [p] [rfWrite k] ∧ PortsRefine t [q] [dmWrite]) := by
  obtain ⟨hw, -⟩ := hi
  obtain ⟨hpc, hhalted, hvalid, hrpc, hrinstr, hrnext, hwbv, hwbr, hwbval, hstv, hsta, hstval, hrhalt, -⟩ := hr
  simp only [Bundle.toVec, HVec.tail_cons, HVec.head_cons] at hw hpc hhalted hvalid hrpc hrinstr hrnext hwbv hwbr hwbval hstv hsta hstval hrhalt
  unfold cpuBody
  rtl_let opc, hopc ← slice_ensures 12 4 hw (by decide) (by decide)
  rtl_let rd, hrd ← slice_ensures 9 3 hw (by decide) (by decide)
  rtl_let rs, hrs ← slice_ensures 6 3 hw (by decide) (by decide)
  rtl_let rt, hrt ← slice_ensures 3 3 hw (by decide) (by decide)
  rtl_let imm, himm ← slice_ensures 0 6 hw (by decide) (by decide)
  rtl_let off, hoff ← slice_ensures 0 8 hw (by decide) (by decide)
  rtl_let z3, hz3 ← const_ensures _ 3 0 (by decide)
  rtl_let z16, hz16 ← const_ensures _ 16 0 (by decide)
  rtl_let ra, hra ← memRead_ensures 0 16 hrs (by decide) (by simp [cpuCtx, cpuMems])
  rtl_let rsz, hrsz ← cmp_ensures .eq hrs hz3
  rtl_let a, ha ← mux_ensures hrsz hz16 hra (by decide)
  rtl_let rb, hrb ← memRead_ensures 0 16 hrt (by decide) (by simp [cpuCtx, cpuMems])
  rtl_let rtz, hrtz ← cmp_ensures .eq hrt hz3
  rtl_let b, hb ← mux_ensures hrtz hz16 hrb (by decide)
  rtl_let rv, hrv ← memRead_ensures 0 16 hrd (by decide) (by simp [cpuCtx, cpuMems])
  rtl_let rdz, hrdz ← cmp_ensures .eq hrd hz3
  rtl_let v, hv ← mux_ensures hrdz hz16 hrv (by decide)
  rtl_let immS, himmS ← sext_ensures 16 himm (by decide) (by decide)
  rtl_let c6, hc6 ← const_ensures _ 4 6 (by decide)
  rtl_let isAddi, hisAddi ← cmp_ensures .eq hopc hc6
  rtl_let bsel, hbsel ← mux_ensures hisAddi himmS hb (by decide)
  rename_i s0
  apply ensures_bind (instantiate_ensures (s := s0) 0 [4, 16, 16] [16] (args := .cons opc (.cons a (.cons bsel .nil)))
    (fa := fun e => .cons (Hw.opc (instrOf e)) (.cons (Hw.a (instrOf e) (rfOf e)) (.cons (Hw.bsel (instrOf e) (rfOf e)) .nil)))
    ⟨hopc, ha, hbsel, trivial⟩ rfl (by decide) (by decide))
  intro alu _ rtl_ext halu
  rtl_mono rtl_ext
  clear rtl_ext
  obtain ⟨hy, -⟩ := halu
  rtl_let eaw, heaw ← bin_ensures .add ha himmS (by decide)
  rtl_let ea, hea ← slice_ensures 0 8 heaw (by decide) (by decide)
  rtl_let ld, hld ← memRead_ensures 1 16 hea (by decide) (by simp [cpuCtx, cpuMems])
  rtl_let c7, hc7 ← const_ensures _ 4 7 (by decide)
  rtl_let c8, hc8 ← const_ensures _ 4 8 (by decide)
  rtl_let c9, hc9 ← const_ensures _ 4 9 (by decide)
  rtl_let c10, hc10 ← const_ensures _ 4 10 (by decide)
  rtl_let isAlu, hisAlu ← cmp_ensures .ult hopc hc7
  rtl_let isLoad, hisLoad ← cmp_ensures .eq hopc hc7
  rtl_let isStore, hisStore ← cmp_ensures .eq hopc hc8
  rtl_let isBeq, hisBeq ← cmp_ensures .eq hopc hc9
  rtl_let isJmp, hisJmp ← cmp_ensures .eq hopc hc10
  rtl_let isHalt, hisHalt ← cmp_ensures .ult hc10 hopc
  rtl_let wbd, hwbd ← mux_ensures hisLoad hld hy (by decide)
  rtl_let wbk, hwbk ← bin_ensures .or hisAlu hisLoad (by decide)
  rtl_let rdnz, hrdnz ← not_ensures hrdz (by decide)
  rtl_let wbe, hwbe ← bin_ensures .and hwbk hrdnz (by decide)
  rtl_let one, hone ← const_ensures _ 8 1 (by decide)
  rtl_let pc1, hpc1 ← bin_ensures .add hpc hone (by decide)
  rtl_let imm8, himm8 ← sext_ensures 8 himm (by decide) (by decide)
  rtl_let br, hbr ← bin_ensures .add hpc1 himm8 (by decide)
  rtl_let jt, hjt ← bin_ensures .add hpc1 hoff (by decide)
  rtl_let tk, htk ← cmp_ensures .eq hv ha
  rtl_let btk, hbtk ← bin_ensures .and hisBeq htk (by decide)
  rtl_let n1, hn1 ← mux_ensures hisHalt hpc hpc1 (by decide)
  rtl_let n2, hn2 ← mux_ensures hbtk hbr hn1 (by decide)
  rtl_let npc, hnpc ← mux_ensures hisJmp hjt hn2 (by decide)
  rtl_let live, hlive ← not_ensures hhalted (by decide)
  rtl_let pcN, hpcN ← mux_ensures hlive hnpc hpc (by decide)
  rtl_let haltN, hhaltN ← bin_ensures .or hhalted hisHalt (by decide)
  rtl_let rfEn, hrfEn ← bin_ensures .and hlive hwbe (by decide)
  rtl_let dmEn, hdmEn ← bin_ensures .and hlive hisStore (by decide)
  refine ensures_pure _ _ ⟨slots s0.cells, ?_, ?_, ?_, _, _, rfl, .cons (port_refines hrfEn hrd hwbd) .nil,
    .cons (port_refines hdmEn hea hv) .nil⟩
  · simp only [BRefines, HRefines, Bundle.toVec, HVec.head_cons, HVec.tail_cons, Hw.out]
    exact ⟨hpc, hvalid, hrpc, hrinstr, hrnext, hwbv, hwbr, hwbval, hstv, hsta, hstval, hrhalt, trivial⟩
  · simp only [BRefines, HRefines, Bundle.toVec, HVec.head_cons, HVec.tail_cons, Hw.next]
    exact ⟨hpcN, hhaltN, hlive, hpc, hw, hnpc, hwbe, hrd, hwbd, hisStore, hea, hv, hisHalt, trivial⟩
  refine ⟨rfl, fun j ps m h1 h2 => ?_⟩
  rcases j with _ | _ | j
  · simp [cpuCtx, cpuMems] at h1 h2
    subst h1; subst h2
    refine ⟨rfl, fun p hp => ?_⟩
    simp at hp; subst hp
    exact ⟨hrfEn.1, hrd.1, hwbd.1⟩
  · simp [cpuCtx, cpuMems] at h1 h2
    subst h1; subst h2
    refine ⟨rfl, fun p hp => ?_⟩
    simp at hp; subst hp
    exact ⟨hdmEn.1, hea.1, hv.1⟩
  · simp at h1

end HDLean.Toy16.Word
