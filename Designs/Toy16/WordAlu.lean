import Designs.Toy16.Word

/-! # The ALU module: what it computes, proved once and used as a black box -/
namespace HDLean.Toy16.Word
open HDLean.Rtl HDLean.Rtl.Build

/-- The ALU's mux tree on the three low opcode bits. -/
def aluHw (op : BitVec 4) (a b : Word) : Word :=
  let lt : Word := (BitVec.ofBool (a.ult b)).setWidth 16
  let o0 := (op.extractLsb' 0 1).getLsbD 0
  let o1 := (op.extractLsb' 1 1).getLsbD 0
  let o2 := (op.extractLsb' 2 1).getLsbD 0
  let m01 := if o0 then a - b else a + b
  let m23 := if o0 then a ||| b else a &&& b
  let m45 := if o0 then lt else a ^^^ b
  let lo := if o1 then m23 else m01
  let hi := if o1 then a + b else m45
  if o2 then hi else lo

theorem aluHw_spec (op : BitVec 4) (a b : Word) (h : op.toNat < 7) : aluHw op a b = aluSpec op a b := by
  have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 := by
    have := op.isLt
    rcases op with ⟨⟨n, hn⟩⟩
    simp only [BitVec.toNat] at h
    rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> simp_all <;> omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [aluHw, aluSpec, BitVec.lt_def, BitVec.ult]
  all_goals by_cases hab : a.toNat < b.toNat <;> simp [hab]

def decAluIn (e : Env) : AluIn BitVec := Bundle.decode AluIn (e.ins.getD · 0)

theorem aluBody_ensures (s : State aluCtx) (i : AluIn Sig) (r : NoFields Sig)
    (hi : BRefines s i decAluIn) :
    Ensures s (aluBody i r) (fun st t => BRefines t st.out (fun e => ⟨aluHw (decAluIn e).op (decAluIn e).a (decAluIn e).b⟩) ∧
      BRefines t st.next (fun _ => ⟨⟩) ∧ WritesOk t st.writes aluCtx.mems) := by
  obtain ⟨hop, ha, hb, -⟩ := hi
  unfold aluBody
  rtl_let s', hs ← bin_ensures .add ha hb (by decide)
  rtl_let d, hd ← bin_ensures .sub ha hb (by decide)
  rtl_let n, hn ← bin_ensures .and ha hb (by decide)
  rtl_let o, ho ← bin_ensures .or ha hb (by decide)
  rtl_let x, hx ← bin_ensures .xor ha hb (by decide)
  rtl_let l1, hl1 ← cmp_ensures .ult ha hb
  rtl_let lt, hlt ← zext_ensures 16 hl1 (by decide) (by decide)
  rtl_let o0, ho0 ← slice_ensures 0 1 hop (by decide) (by decide)
  rtl_let o1, ho1 ← slice_ensures 1 1 hop (by decide) (by decide)
  rtl_let o2, ho2 ← slice_ensures 2 1 hop (by decide) (by decide)
  rtl_let m01, hm01 ← mux_ensures ho0 hd hs (by decide)
  rtl_let m23, hm23 ← mux_ensures ho0 ho hn (by decide)
  rtl_let m45, hm45 ← mux_ensures ho0 hlt hx (by decide)
  rtl_let lo, hlo ← mux_ensures ho1 hm23 hm01 (by decide)
  rtl_let hi', hhi ← mux_ensures ho1 hs hm45 (by decide)
  rtl_let y, hy ← mux_ensures ho2 hhi hlo (by decide)
  exact ensures_pure _ _ ⟨⟨⟨hy.1, fun e => hy.2 e⟩, trivial⟩, trivial, WritesOk.nil⟩

theorem aluCtx_ok : aluCtx.ok = true := by decide

/-- The ALU module's output, for every environment, store and reset. -/
theorem alu_output (env : Nat → Sem) (st : Store) (ins : Array Nat) (rst : Bool) :
    Bundle.decode AluOut ((aluModule.evalWith env st ins rst).1.getD · 0) =
      ⟨aluHw (Bundle.decode AluIn (ins.getD · 0)).op (Bundle.decode AluIn (ins.getD · 0)).a
        (Bundle.decode AluIn (ins.getD · 0)).b⟩ := by
  obtain ⟨t, sp, hm, ho, -, -⟩ := mealy_build aluCtx_ok aluBody _ (fun _ => ⟨⟩)
    (fun s i r hi _ => aluBody_ensures s i r hi)
  have hm' : aluModule = _ := hm
  rw [hm']
  exact mealy_outputs t sp _ ho env st ins rst

end HDLean.Toy16.Word
