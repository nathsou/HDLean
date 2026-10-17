import HDLean.Rtl.Blast.Module
import HDLean.Rtl.Memory
import HDLean.Rtl.Design

/-!
# Designs whose top is a finished Mealy module

What a design proof needs once `mealy_build` has run, stated for the design
rather than the module: the next registers and the outputs as records
(`mealy_step`, `mealy_output`), each memory word (`mealy_step_mem`), the Moore
property when the output specification ignores the inputs (`mealy_isMoore`),
and the state budget (`mealy_stateBits`).

`Blast.stateBits` counts flip-flop and memory bits. For a module produced by
the builder, the cells are only known through the builder's proof, so `decide`
cannot count them; a builder module with no submodules instantiates nothing, so
its state is exactly its registers and memories.
-/
namespace HDLean.Rtl
open Build

theorem cellsValidFrom_noInst {sc : Scope} (hs : sc.subs = #[]) :
    ∀ {ws : Array Nat} {cs : List Cell}, cellsValidFrom sc ws cs = true →
      cs.filterMap (fun c => match c.op with | .inst j _ _ => some j | _ => none) = []
  | _, [], _ => rfl
  | ws, c :: cs, h => by
    simp only [cellsValidFrom, Bool.and_eq_true] at h
    obtain ⟨⟨-, hv⟩, hrest⟩ := h
    have hc : (match c.op with | .inst j _ _ => some j | _ => none) = (none : Option Nat) := by
      cases hop : c.op <;> simp_all [Op.valid]
    rw [List.filterMap_cons, hc]
    exact cellsValidFrom_noInst hs hrest

theorem Build.State.instMods_toModule {c : Ctx} (t : State c) (r : Wiring) (hs : c.subs = #[]) :
    Blast.instMods (t.toModule r) = [] :=
  cellsValidFrom_noInst (sc := c.scope) hs t.valid

theorem Blast.stateBits_leaf {d : Design} {k : Nat} {m : Module} (hm : d.modules[k]? = some m)
    (hi : instMods m = []) : stateBits d k = regBits m + memBits m := by
  rw [stateBits, hm]; simp only [hi]; rfl

/-- A builder module's state bits: its registers and memories, as declared by the context. -/
theorem Build.State.stateBits_toModule {c : Ctx} {d : Design} {k : Nat} (t : State c) (r : Wiring)
    (hm : d.modules[k]? = some (t.toModule r)) (hs : c.subs = #[]) :
    Blast.stateBits d k = ((c.regs.zip r.nexts).toList.map fun p => p.1.width).sum +
      ((c.mems.zip r.writes).toList.map fun p => 2 ^ p.1.addrWidth * p.1.width).sum := by
  rw [Blast.stateBits_leaf hm (t.instMods_toModule r hs)]
  simp [Blast.regBits, Blast.memBits, State.toModule, Function.comp_def]

theorem Build.State.stateBits_toModule_of_fits {c : Ctx} {d : Design} {k : Nat} (t : State c) (r : Wiring)
    (hm : d.modules[k]? = some (t.toModule r)) (hs : c.subs = #[])
    (hr : c.regs.size ≤ r.nexts.size) (hw : c.mems.size ≤ r.writes.size) :
    Blast.stateBits d k = (c.regs.toList.map RegSpec.width).sum +
      (c.mems.toList.map fun m => 2 ^ m.addrWidth * m.width).sum := by
  rw [t.stateBits_toModule r hm hs]
  congr 2
  · rw [show (fun p : RegSpec × Nat => p.1.width) = RegSpec.width ∘ Prod.fst from rfl, ← List.map_map,
      Array.toList_zip, List.map_fst_zip (by simpa using hr)]
  · rw [show (fun p : MemSpec × Array WritePort => 2 ^ p.1.addrWidth * p.1.width) =
      (fun m : MemSpec => 2 ^ m.addrWidth * m.width) ∘ Prod.fst from rfl, ← List.map_map,
      Array.toList_zip, List.map_fst_zip (by simpa using hw)]

section
variable {name : String} {I O R : (Nat → Type) → Type} [Bundle I] [Bundle O] [Bundle R]
  {resets : R (fun _ => Reset)} {mems : Array MemSpec} {subs : Array (List Nat × List Nat)}

theorem Ctx.mealy_regs_widths :
    (Ctx.mealy name I O R resets mems subs).regs.toList.map RegSpec.width = Bundle.widths R := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map, Array.getElem?_toList]
  simp only [Ctx.mealy_regs, Array.getElem?_map, List.getElem?_toArray, List.getElem?_map, Option.map_map]
  rw [show ∀ (l : List ((String × Nat) × Reset)), Option.map (RegSpec.width ∘
      fun p => (⟨Ident.ofString p.1.1, p.1.2, p.2⟩ : RegSpec)) l[k]? = (l.map (Prod.snd ∘ Prod.fst))[k]? from
      fun l => by rw [List.getElem?_map]; rfl]
  rw [← List.map_map, List.map_fst_zip (by simp), List.getElem?_map]

/-- The state bits of a Mealy module built without submodules: its register
widths and its memory sizes. -/
theorem mealy_stateBits {d : Design} {k : Nat} (t : State (Ctx.mealy name I O R resets mems subs))
    (st : Step O R) (hm : d.modules[k]? = some (t.toModule
      ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩))
    (hw : WritesOk t st.writes mems) (hs : subs = #[]) :
    Blast.stateBits d k = (Bundle.widths R).sum + (mems.toList.map fun m => 2 ^ m.addrWidth * m.width).sum := by
  rw [t.stateBits_toModule_of_fits _ hm hs (by simp [refs]) (by simp [hw.1]), Ctx.mealy_regs_widths]
  rfl

/-- Values of handles whose specification agrees in two environments agree. -/
theorem HRefines.val_congr {t : State c} (e e' : Env) :
    ∀ {ws : List Nat} {v : HVec Sig ws} {f : Env → HVec BitVec ws}, HRefines t v f → f e = f e' →
      ∀ k ∈ v.toList Sig.ref, t.val e k = t.val e' k
  | [], .nil, _, _, _, k, hk => by simp [HVec.toList] at hk
  | _ :: _, .cons x xs, f, h, hf, k, hk => by
    simp only [HVec.toList, List.mem_cons] at hk
    have hh : (f e).head = (f e').head := by rw [hf]
    have ht : (fun e => (f e).tail) e = (fun e => (f e).tail) e' := by simp only [hf]
    rcases hk with rfl | hk
    · exact (h.1.2 e).trans ((congrArg BitVec.toNat hh).trans (h.1.2 e').symm)
    · exact HRefines.val_congr e e' h.2 ht k hk

variable {d : Design} {t : State (Ctx.mealy name I O R resets mems subs)} {st : Step O R}

/-- The next registers of the design, decoded: the register specification, after resets. -/
theorem mealy_step (hd : d.modules[d.top]? = some (t.toModule
      ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩))
    {specR : Env → R BitVec} (hn : BRefines t st.next specR) (s : Store) (x : Array Nat × Bool) :
    Bundle.decode R ((d.step s x).regs.getD · 0) = Bundle.reset x.2 resets (specR ⟨d.env d.top, s, x.1, x.2⟩) := by
  rw [Design.step_eq _ _ hd]
  exact mealy_regs t st specR hn _ s x.1 x.2

/-- The outputs of the design, decoded: the output specification. -/
theorem mealy_output (hd : d.modules[d.top]? = some (t.toModule
      ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩))
    {specO : Env → O BitVec} (ho : BRefines t st.out specO) (s : Store) (ins : Array Nat) :
    Bundle.decode O ((d.output s ins).getD · 0) = specO ⟨d.env d.top, s, ins, false⟩ := by
  rw [Design.output_eq _ _ hd]
  exact mealy_outputs t st specO ho _ s ins false

/-- A Mealy design whose output specification ignores the inputs is a Moore design. -/
theorem mealy_isMoore (hd : d.modules[d.top]? = some (t.toModule
      ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩))
    {specO : Env → O BitVec} (ho : BRefines t st.out specO)
    (hi : ∀ env s a b, specO ⟨env, s, a, false⟩ = specO ⟨env, s, b, false⟩) : d.IsMoore := by
  intro s a b
  rw [Design.output_eq _ _ hd, Design.output_eq _ _ hd, toModule_evalWith, toModule_evalWith]
  apply Array.ext (by simp)
  intro i h1 h2
  simp only [Array.getElem_map]
  apply HRefines.val_congr _ _ ho (by simp only [hi _ s a b])
  simp only [State.toModule, Array.getElem_map, Array.getElem_zip, refs]
  exact List.getElem_mem _

/-- Each word of memory `i` after a step: the write specifications applied to the old word. -/
theorem mealy_step_mem (hd : d.modules[d.top]? = some (t.toModule
      ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩))
    (i : Nat) (ms : MemSpec) (ps : Array WritePort) (specs : List (WriteSpec ms.addrWidth ms.width))
    (hm : mems[i]? = some ms) (hw : st.writes[i]? = some ps) (hp : PortsRefine t ps.toList specs)
    (s : Store) (x : Array Nat × Bool) (a : BitVec ms.addrWidth) :
    (d.step s x).mem i ms.addrWidth ms.width a =
      WriteSpec.apply specs ⟨d.env d.top, s, x.1, x.2⟩ a (s.mem i ms.addrWidth ms.width a) := by
  rw [Design.step_eq _ _ hd]
  exact mealy_mem t st i ms ps specs hm hw hp _ s x.1 x.2 a

end

end HDLean.Rtl
