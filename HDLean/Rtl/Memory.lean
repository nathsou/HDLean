import HDLean.Rtl.Design

/-!
# Memories in specifications

A memory is read as a function from addresses to words (`Mem.read`). After a
cycle, every address holds the data of the last enabled write port aimed at it,
or its old word (`WriteSpec.apply`). `mealy_mem` states this for a finished
Mealy module whose write ports refine `WriteSpec`s, so proofs never look at
arrays.
-/
namespace HDLean.Rtl

/-- The word at address `a` of a memory's contents. -/
def memWord (w : Nat) (arr : Array Nat) (a : Nat) : BitVec w := bv w (arr.getD a 0)

/-- A memory of the store as a function of the address. -/
def Store.mem (st : Store) (i aw w : Nat) : BitVec aw → BitVec w := fun a => memWord w (st.mems.getD i #[]) a.toNat

theorem Mem.foldl_size (v : Nat → Nat) (w : Nat) : ∀ (ps : List WritePort) (arr : Array Nat),
    (ps.foldl (fun arr p => if (v p.en).testBit 0 then arr.setIfInBounds (v p.addr) (bv w (v p.data)).toNat else arr)
      arr).size = arr.size
  | [], _ => rfl
  | p :: ps, arr => by
    simp only [List.foldl_cons]
    rw [Mem.foldl_size v w ps]
    split <;> simp

theorem Mem.foldl_getD (v : Nat → Nat) (w a : Nat) : ∀ (ps : List WritePort) (arr : Array Nat), a < arr.size →
    (ps.foldl (fun arr p => if (v p.en).testBit 0 then arr.setIfInBounds (v p.addr) (bv w (v p.data)).toNat else arr)
      arr).getD a 0 =
      ps.foldl (fun x p => if (v p.en).testBit 0 ∧ v p.addr = a then (bv w (v p.data)).toNat else x) (arr.getD a 0)
  | [], _, _ => rfl
  | p :: ps, arr, h => by
    simp only [List.foldl_cons]
    rw [Mem.foldl_getD v w a ps _ (by split <;> simp [h])]
    congr 1
    by_cases he : (v p.en).testBit 0
    · rw [if_pos he]
      by_cases ha : v p.addr = a
      · rw [if_pos ⟨he, ha⟩, ha, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt h]; rfl
      · rw [if_neg (fun h' => ha h'.2), Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne ha,
          ← Array.getD_eq_getD_getElem?]
    · rw [if_neg he, if_neg (fun h' => he h'.1)]

theorem Mem.update_getD (v : Nat → Nat) (mm : Mem) (old : Array Nat) (a : Nat) (ha : a < 2 ^ mm.addrWidth) :
    (mm.update v old).getD a 0 = mm.writes.toList.foldl
      (fun x p => if (v p.en).testBit 0 ∧ v p.addr = a then (bv mm.width (v p.data)).toNat else x) (old.getD a 0) := by
  unfold Mem.update
  have hs : (mm.shape old).size = 2 ^ mm.addrWidth := by unfold Mem.shape; split <;> simp_all
  rw [← Array.foldl_toList, Mem.foldl_getD v mm.width a _ _ (by rw [hs]; exact ha)]
  congr 1
  unfold Mem.shape; split
  · rfl
  · simp [ha]

namespace Build

/-- What a write port does, as functions of the environment. -/
structure WriteSpec (aw w : Nat) where
  en : Env → Bool
  addr : Env → BitVec aw
  data : Env → BitVec w

/-- The word at `a` after the writes, later ports winning. -/
def WriteSpec.apply (specs : List (WriteSpec aw w)) (e : Env) (a : BitVec aw) (old : BitVec w) : BitVec w :=
  specs.foldl (fun x s => if s.en e ∧ s.addr e = a then s.data e else x) old


/-- A write port from typed signals. -/
def port (en : Sig 1) (addr : Sig aw) (data : Sig w) : WritePort := ⟨en.ref, addr.ref, data.ref⟩

/-- A raw write port computes what its specification says. -/
def PortRefines (t : State c) (p : WritePort) (s : WriteSpec aw w) : Prop :=
  t.widths[p.en]? = some 1 ∧ t.widths[p.addr]? = some aw ∧ t.widths[p.data]? = some w ∧
  ∀ e, (t.val e p.en).testBit 0 = s.en e ∧ t.val e p.addr = (s.addr e).toNat ∧ bv w (t.val e p.data) = s.data e

theorem port_refines {t : State c} {en : Sig 1} {addr : Sig aw} {data : Sig w} {fe fa fd}
    (he : Refines t en fe) (ha : Refines t addr fa) (hd : Refines t data fd) :
    PortRefines t (port en addr data) ⟨fun e => (fe e).getLsbD 0, fa, fd⟩ :=
  ⟨he.1, ha.1, hd.1, fun e => ⟨by simp [port, he.2 e, BitVec.getLsbD], ha.2 e, by simp [port, hd.2 e]⟩⟩

theorem PortRefines.mono {s t : State c} {p : WritePort} {sp : WriteSpec aw w} (h : PortRefines s p sp)
    (hx : Extends s t) : PortRefines t p sp := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hv : ∀ e k, s.widths[k]?.isSome → t.val e k = s.val e k := by
    intro e k hk
    have hlt : k < s.cells.size := by
      rw [s.widths_eq] at hk
      rcases Nat.lt_or_ge k s.cells.size with hl | hl
      · exact hl
      · simp [Array.getElem?_eq_none (by simpa using hl)] at hk
    exact hx.val e hlt
  exact ⟨hx.widths h1, hx.widths h2, hx.widths h3, fun e => by
    rw [hv e _ (by simp [h1]), hv e _ (by simp [h2]), hv e _ (by simp [h3])]; exact h4 e⟩

/-- Write ports and their specifications, pairwise. -/
inductive PortsRefine (t : State c) : List WritePort → List (WriteSpec aw w) → Prop
  | nil : PortsRefine t [] []
  | cons {p ps s specs} : PortRefines t p s → PortsRefine t ps specs → PortsRefine t (p :: ps) (s :: specs)

theorem PortsRefine.mono {s t : State c} (hx : Extends s t) :
    ∀ {ps : List WritePort} {specs : List (WriteSpec aw w)}, PortsRefine s ps specs → PortsRefine t ps specs
  | _, _, .nil => .nil
  | _, _, .cons hp hr => .cons (hp.mono hx) (PortsRefine.mono hx hr)

theorem foldl_ports {t : State c} (e : Env) (aw w : Nat) (a : BitVec aw) :
    ∀ (ps : List WritePort) (specs : List (WriteSpec aw w)) (x : Nat),
      PortsRefine t ps specs →
      bv w (ps.foldl (fun x p => if (t.val e p.en).testBit 0 ∧ t.val e p.addr = a.toNat then
          (bv w (t.val e p.data)).toNat else x) x) = WriteSpec.apply specs e a (bv w x)
  | [], [], _, _ => rfl
  | p :: ps, s :: specs, x, .cons hp hr => by
    simp only [List.foldl_cons, WriteSpec.apply]
    rw [foldl_ports e aw w a ps specs _ hr]
    unfold WriteSpec.apply
    congr 1
    obtain ⟨-, -, -, h⟩ := hp
    obtain ⟨he, ha, hd⟩ := h e
    rw [he, ha]
    by_cases hc : s.en e = true ∧ s.addr e = a
    · rw [if_pos ⟨hc.1, by rw [hc.2]⟩, if_pos hc, bv_toNat, hd]
    · have : ¬ (s.en e = true ∧ (s.addr e).toNat = a.toNat) := fun h' => hc ⟨h'.1, BitVec.eq_of_toNat_eq h'.2⟩
      rw [if_neg this, if_neg hc]

variable {name : String} {I O R : (Nat → Type) → Type} [Bundle I] [Bundle O] [Bundle R]
  {resets : R (fun _ => Reset)} {mems : Array MemSpec} {subs : Array (List Nat × List Nat)}

/-- Memory `i` of a finished Mealy module after one cycle, read as a function. -/
theorem mealy_mem (t : State (Ctx.mealy name I O R resets mems subs)) (st : Step O R) (i : Nat) (ms : MemSpec)
    (ps : Array WritePort) (specs : List (WriteSpec ms.addrWidth ms.width))
    (hm : mems[i]? = some ms) (hw : st.writes[i]? = some ps) (hp : PortsRefine t ps.toList specs)
    (env : Nat → Sem) (store : Store) (ins : Array Nat) (rst : Bool) (a : BitVec ms.addrWidth) :
    (((t.toModule ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩).evalWith
      env store ins rst).2.mem i ms.addrWidth ms.width) a =
      WriteSpec.apply specs ⟨env, store, ins, rst⟩ a (store.mem i ms.addrWidth ms.width a) := by
  rw [toModule_evalWith]
  have hz : ((mems.zip st.writes).map fun p => (⟨p.1.name, p.1.addrWidth, p.1.width, p.2⟩ : Mem))[i]? =
      some ⟨ms.name, ms.addrWidth, ms.width, ps⟩ := by
    simp [Array.zip, Array.getElem?_zipWith, hm, hw]
  simp only [Store.mem, memWord, Array.getD_eq_getD_getElem?, Store.mems_mk, Array.getElem?_mapIdx, State.toModule,
    Ctx.mealy_mems, hz, Option.map_some, Option.getD_some]
  rw [← Array.getD_eq_getD_getElem?, Mem.update_getD _ _ _ _ a.isLt]
  simp only [← Array.getD_eq_getD_getElem?]
  exact foldl_ports _ ms.addrWidth ms.width a ps.toList specs _ hp

theorem zipWith_resetField_false : ∀ {ws : List Nat} (rs : HVec (fun _ => Reset) ws) (v : HVec BitVec ws),
    HVec.zipWith (resetField false) rs v = v
  | [], .nil, .nil => rfl
  | _ :: _, .cons r rs, .cons x xs => by
    simp only [HVec.zipWith, zipWith_resetField_false rs xs]
    cases r <;> rfl

/-- Reset low leaves the next register record as computed. -/
@[simp] theorem _root_.HDLean.Rtl.Bundle.reset_false {R : (Nat → Type) → Type} [Bundle R]
    (resets : R (fun _ => Reset)) (r : R BitVec) : Bundle.reset false resets r = r := by
  unfold Bundle.reset
  rw [zipWith_resetField_false, Bundle.ofVec_toVec]

/-- `mealy_build` with an extra property of the final builder state, such as
the refinement of memory write ports or of instance outputs. -/
theorem mealy_build_with (hc : (Ctx.mealy name I O R resets mems subs).ok = true)
    (body : I Sig → R Sig → M (Ctx.mealy name I O R resets mems subs) (Step O R))
    (specO : Env → O BitVec) (specR : Env → R BitVec)
    (P : Step O R → State (Ctx.mealy name I O R resets mems subs) → Prop)
    (hbody : ∀ s ins regs, BRefines s ins (fun e => Bundle.decode I (e.ins.getD · 0)) →
      BRefines s regs (fun e => Bundle.decode R (e.st.regs.getD · 0)) →
      Ensures s (body ins regs) (fun st t => BRefines t st.out specO ∧ BRefines t st.next specR ∧
        WritesOk t st.writes mems ∧ P st t)) :
    ∃ (t : State (Ctx.mealy name I O R resets mems subs)) (st : Step O R),
      (Ctx.mealy name I O R resets mems subs).module (mealy I O R body) =
        t.toModule ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩ ∧
      BRefines t st.out specO ∧ BRefines t st.next specR ∧ WritesOk t st.writes mems ∧ P st t := by
  obtain ⟨hpI, hpR⟩ := Ctx.mealy_ok_pos hc
  obtain ⟨r, t, hp, -, st, hpost, rfl⟩ := mealy_ensures I O R body _
    Ctx.mealy_input_widths Ctx.mealy_reg_widths hpI hpR hbody
  exact ⟨t, st, Ctx.module_eq hp hc (mealy_wired t st hpost.1 hpost.2.1 hpost.2.2.1.1 hpost.2.2.1.2),
    hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2⟩

/-- `mealy_build_with` where the specifications may depend on a value chosen
inside the proof of the body, such as the store slot of an instance. -/
theorem mealy_build_ex {κ : Type} (hc : (Ctx.mealy name I O R resets mems subs).ok = true)
    (body : I Sig → R Sig → M (Ctx.mealy name I O R resets mems subs) (Step O R))
    (specO : κ → Env → O BitVec) (specR : κ → Env → R BitVec)
    (P : κ → Step O R → State (Ctx.mealy name I O R resets mems subs) → Prop)
    (hbody : ∀ s ins regs, BRefines s ins (fun e => Bundle.decode I (e.ins.getD · 0)) →
      BRefines s regs (fun e => Bundle.decode R (e.st.regs.getD · 0)) →
      Ensures s (body ins regs) (fun st t => ∃ k, BRefines t st.out (specO k) ∧ BRefines t st.next (specR k) ∧
        WritesOk t st.writes mems ∧ P k st t)) :
    ∃ (t : State (Ctx.mealy name I O R resets mems subs)) (st : Step O R) (k : κ),
      (Ctx.mealy name I O R resets mems subs).module (mealy I O R body) =
        t.toModule ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩ ∧
      BRefines t st.out (specO k) ∧ BRefines t st.next (specR k) ∧ WritesOk t st.writes mems ∧ P k st t := by
  obtain ⟨hpI, hpR⟩ := Ctx.mealy_ok_pos hc
  obtain ⟨r, t, hp, -, st, ⟨k, hpost⟩, rfl⟩ := mealy_ensures I O R body _
    Ctx.mealy_input_widths Ctx.mealy_reg_widths hpI hpR hbody
  exact ⟨t, st, k, Ctx.module_eq hp hc (mealy_wired t st hpost.1 hpost.2.1 hpost.2.2.1.1 hpost.2.2.1.2),
    hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2⟩

end Build
end HDLean.Rtl
