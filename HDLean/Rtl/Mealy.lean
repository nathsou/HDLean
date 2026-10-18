import HDLean.Rtl.Bundle

/-!
# Mealy-style modules over typed records

`mealy body` reads the input record and the register record, runs `body`, and
wires the returned output record, next-register record and memory write ports.
`mealy_run` turns a compositional proof of `body` into the cycle semantics of the
finished module, stated over the semantic records.
-/
namespace HDLean.Rtl.Build

/-- A module interface built from typed records. -/
def Ctx.mealy (name : String) (I O R : (Nat → Type) → Type) [Bundle I] [Bundle O] [Bundle R]
    (resets : R (fun _ => Reset)) (mems : Array MemSpec := #[])
    (subs : Array (List Nat × List Nat) := #[]) : Ctx where
  name := Ident.ofString name
  inputs := Bundle.ports I
  outputs := Bundle.ports O
  regs := (((Bundle.fields R).zip ((Bundle.toVec resets).toList (fun r => r))).map
    fun p => (⟨Ident.ofString p.1.1, p.1.2, p.2⟩ : RegSpec)).toArray
  mems := mems
  subs := subs

def readInputs : (ws : List Nat) → (base : Nat) → M c (HVec Sig ws)
  | [], _ => pure .nil
  | w :: ws, base => do
    let x ← input base w
    let xs ← readInputs ws (base + 1)
    pure (.cons x xs)

def readRegs : (ws : List Nat) → (base : Nat) → M c (HVec Sig ws)
  | [], _ => pure .nil
  | w :: ws, base => do
    let x ← regRead base w
    let xs ← readRegs ws (base + 1)
    pure (.cons x xs)

/-- What one cycle drives. -/
structure Step (O R : (Nat → Type) → Type) where
  out : O Sig
  next : R Sig
  writes : Array (Array WritePort) := #[]

def refs (v : HVec Sig ws) : Array Nat := (v.toList Sig.ref).toArray

def mealy (I O R : (Nat → Type) → Type) [Bundle I] [Bundle O] [Bundle R]
    (body : I Sig → R Sig → M c (Step O R)) : M c Wiring := do
  let ins ← readInputs (Bundle.widths I) 0
  let regs ← readRegs (Bundle.widths R) 0
  let r ← body (Bundle.ofVec ins) (Bundle.ofVec regs)
  pure ⟨refs (Bundle.toVec r.out), refs (Bundle.toVec r.next), r.writes⟩

/-! ## Specifications over records -/

def HRefines (t : State c) : {ws : List Nat} → HVec Sig ws → (Env → HVec BitVec ws) → Prop
  | [], _, _ => True
  | _ :: _, v, f => Refines t v.head (fun e => (f e).head) ∧ HRefines t v.tail (fun e => (f e).tail)

theorem HRefines.mono {s t : State c} :
    ∀ {ws : List Nat} {v : HVec Sig ws} {f}, HRefines s v f → Extends s t → HRefines t v f
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, h, hx => ⟨h.1.mono hx, HRefines.mono h.2 hx⟩

/-- Every field of a handle record carries the matching field of `f e`. -/
def BRefines {R : (Nat → Type) → Type} [Bundle R] (t : State c) (r : R Sig) (f : Env → R BitVec) : Prop :=
  HRefines t (Bundle.toVec r) (fun e => Bundle.toVec (f e))

theorem BRefines.mono {R : (Nat → Type) → Type} [Bundle R] {s t : State c} {r : R Sig} {f}
    (h : BRefines s r f) (hx : Extends s t) : BRefines t r f := HRefines.mono h hx


theorem readInputs_ensures (s : State c) (ws : List Nat) (base : Nat) (hpos : ∀ w ∈ ws, 0 < w)
    (hk : ∀ (k : Nat), (c.inputs[base + k]?).map Port.width = ws[k]? ∨ ws.length ≤ k) :
    Ensures s (readInputs ws base) (fun v t => HRefines t v (fun e => HVec.decode ws base (e.ins.getD · 0))) := by
  induction ws generalizing s base with
  | nil => exact ensures_pure _ _ trivial
  | cons w ws ih =>
    have h0 : (c.inputs[base]?).map Port.width = some w := by
      rcases hk 0 with h | h
      · simpa using h
      · simp at h
    unfold readInputs
    rtl_let x, hx ← input_ensures _ base w (hpos w (by simp)) h0
    apply ensures_bind (ih _ (base + 1) (fun v hv => hpos v (by simp [hv]))
      (fun k => by rcases hk (k + 1) with h | h
                   · left; simpa [Nat.add_assoc, Nat.add_comm 1 k] using h
                   · right; simp at h; omega))
    intro xs t ext hxs
    exact ensures_pure _ _ ⟨hx.mono ext, hxs⟩

theorem readRegs_ensures (s : State c) (ws : List Nat) (base : Nat) (hpos : ∀ w ∈ ws, 0 < w)
    (hk : ∀ (k : Nat), (c.regs[base + k]?).map RegSpec.width = ws[k]? ∨ ws.length ≤ k) :
    Ensures s (readRegs ws base) (fun v t => HRefines t v (fun e => HVec.decode ws base (e.st.regs.getD · 0))) := by
  induction ws generalizing s base with
  | nil => exact ensures_pure _ _ trivial
  | cons w ws ih =>
    have h0 : (c.regs[base]?).map RegSpec.width = some w := by
      rcases hk 0 with h | h
      · simpa using h
      · simp at h
    unfold readRegs
    rtl_let x, hx ← regRead_ensures _ base w (hpos w (by simp)) h0
    apply ensures_bind (ih _ (base + 1) (fun v hv => hpos v (by simp [hv]))
      (fun k => by rcases hk (k + 1) with h | h
                   · left; simpa [Nat.add_assoc, Nat.add_comm 1 k] using h
                   · right; simp at h; omega))
    intro xs t ext hxs
    exact ensures_pure _ _ ⟨hx.mono ext, hxs⟩


/-! ## From a proved body to the cycle semantics -/

/-- Field-wise effect of reset on a register value. -/
def resetField (rst : Bool) : Reset → BitVec w → BitVec w
  | .sync v, x => if rst then bv w v else x
  | .none, x => x

/-- Apply the declared resets to a semantic register record. -/
def _root_.HDLean.Rtl.Bundle.reset {R : (Nat → Type) → Type} [Bundle R] (rst : Bool)
    (resets : R (fun _ => Reset)) (r : R BitVec) : R BitVec :=
  Bundle.ofVec (HVec.zipWith (resetField rst) (Bundle.toVec resets) (Bundle.toVec r))

theorem decode_outputs (t : State c) (e : Env) :
    ∀ {ws : List Nat} (v : HVec Sig ws) (f : Env → HVec BitVec ws) (pre : List Nat),
      HRefines t v f →
      HVec.decode ws pre.length (fun k => (pre ++ v.toList (fun x => t.val e x.ref)).getD k 0) = f e
  | [], .nil, f, _, _ => by cases f e; rfl
  | w :: ws, .cons x xs, f, pre, h => by
    simp only [HVec.decode, HVec.toList]
    have hx := h.1.bv e
    have ih := decode_outputs t e xs (fun e => (f e).tail) (pre ++ [t.val e x.ref]) h.2
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at ih
    rw [HVec.eta (f e), ih]
    congr 1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
    exact hx

theorem decode_regs (t : State c) (e : Env) (rst : Bool) :
    ∀ (fs : List (String × Nat)) (rs : HVec (fun _ => Reset) (fs.map Prod.snd))
      (v : HVec Sig (fs.map Prod.snd)) (f : Env → HVec BitVec (fs.map Prod.snd)) (pre : List Nat),
      HRefines t v f →
      HVec.decode (fs.map Prod.snd) pre.length (fun k => (pre ++ ((fs.zip (rs.toList (fun r => r))).zip
        (v.toList Sig.ref)).map (fun p => Reg.update rst (t.val e) ⟨Ident.ofString p.1.1.1, p.1.1.2, p.1.2, p.2⟩)).getD k 0) =
        HVec.zipWith (resetField rst) rs (f e)
  | [], .nil, .nil, f, _, _ => by cases f e; rfl
  | (n, w) :: fs, .cons r rs, .cons x xs, f, pre, h => by
    change HVec.decode (w :: fs.map Prod.snd) pre.length _ = HVec.zipWith _ (HVec.cons r rs) (f e)
    simp only [HVec.decode, HVec.toList, List.zip_cons_cons, List.map_cons]
    have hx := h.1.2 e
    have ih := decode_regs t e rst fs rs xs (fun e => (f e).tail) (pre ++ [Reg.update rst (t.val e)
      ⟨Ident.ofString n, w, r, x.ref⟩]) h.2
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at ih
    rw [HVec.eta (f e), ih]
    simp only [HVec.zipWith, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    congr 1
    have hv : t.val e x.ref = ((f e).head).toNat := hx
    cases r with
    | none => simp [Reg.update, resetField, hv]
    | sync v => cases rst <;> simp [Reg.update, resetField, hv]

theorem mealy_ensures (I O R : (Nat → Type) → Type) [Bundle I] [Bundle O] [Bundle R]
    (body : I Sig → R Sig → M c (Step O R)) (post : Step O R → State c → Prop)
    (hI : ∀ (k : Nat), (c.inputs[k]?).map Port.width = (Bundle.widths I)[k]? ∨ (Bundle.widths I).length ≤ k)
    (hR : ∀ (k : Nat), (c.regs[k]?).map RegSpec.width = (Bundle.widths R)[k]? ∨ (Bundle.widths R).length ≤ k)
    (hposI : ∀ w ∈ Bundle.widths I, 0 < w) (hposR : ∀ w ∈ Bundle.widths R, 0 < w)
    (hbody : ∀ s ins regs, BRefines s ins (fun e => Bundle.decode I (e.ins.getD · 0)) →
      BRefines s regs (fun e => Bundle.decode R (e.st.regs.getD · 0)) → Ensures s (body ins regs) post) :
    Ensures (init c) (mealy I O R body) (fun r t => ∃ st, post st t ∧
      r = ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩) := by
  unfold mealy
  apply ensures_bind (readInputs_ensures _ _ 0 hposI (by simpa using hI))
  intro ins t1 e1 hins
  apply ensures_bind (readRegs_ensures _ _ 0 hposR (by simpa using hR))
  intro regs t2 e2 hregs
  have hins' : BRefines t2 (Bundle.ofVec ins : I Sig) (fun e => Bundle.decode I (e.ins.getD · 0)) := by
    unfold BRefines Bundle.decode; simpa [Bundle.toVec_ofVec] using hins.mono e2
  have hregs' : BRefines t2 (Bundle.ofVec regs : R Sig) (fun e => Bundle.decode R (e.st.regs.getD · 0)) := by
    unfold BRefines Bundle.decode; simpa [Bundle.toVec_ofVec] using hregs
  apply ensures_bind (hbody t2 _ _ hins' hregs')
  intro st t3 e3 hpost
  exact ensures_pure _ _ ⟨st, hpost, rfl⟩


@[simp] theorem HVec.toList_length (f : ∀ {w}, F w → α) :
    ∀ {ws : List Nat} (v : HVec F ws), (v.toList f).length = ws.length
  | [], .nil => rfl
  | _ :: _, .cons _ xs => by simp [HVec.toList, HVec.toList_length f xs]

theorem HVec.toList_map_ref (t : State c) (e : Env) :
    ∀ {ws : List Nat} (v : HVec Sig ws), (v.toList Sig.ref).map (t.val e) = v.toList (fun x => t.val e x.ref)
  | [], .nil => rfl
  | _ :: _, .cons _ xs => by simp [HVec.toList, HVec.toList_map_ref t e xs]

section
variable {name : String} {I O R : (Nat → Type) → Type} [Bundle I] [Bundle O] [Bundle R]
  {resets : R (fun _ => Reset)} {mems : Array MemSpec} {subs : Array (List Nat × List Nat)}

@[simp] theorem Ctx.mealy_outputs : (Ctx.mealy name I O R resets mems subs).outputs = Bundle.ports O := rfl
@[simp] theorem Ctx.mealy_mems : (Ctx.mealy name I O R resets mems subs).mems = mems := rfl
@[simp] theorem Ctx.mealy_inputs : (Ctx.mealy name I O R resets mems subs).inputs = Bundle.ports I := rfl
@[simp] theorem Ctx.mealy_regs : (Ctx.mealy name I O R resets mems subs).regs =
    ((Bundle.fields R).zip ((Bundle.toVec resets).toList (fun r => r))).toArray.map
      (fun p => ⟨Ident.ofString p.1.1, p.1.2, p.2⟩) := by simp [Ctx.mealy]

theorem getD_toList (a : Array Nat) (k : Nat) : a.getD k 0 = a.toList.getD k 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- Outputs of a finished Mealy module, decoded into the output record. -/
theorem mealy_outputs (t : State (Ctx.mealy name I O R resets mems subs)) (st : Step O R)
    (specO : Env → O BitVec) (ho : BRefines t st.out specO) (env store ins rst) :
    Bundle.decode O (((t.toModule ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩).evalWith
      env store ins rst).1.getD · 0) = specO ⟨env, store, ins, rst⟩ := by
  have hl : ∀ x, (((t.toModule ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩).evalWith
      env store ins rst).1.getD x 0) =
      (((Bundle.toVec st.out).toList (fun y => t.val ⟨env, store, ins, rst⟩ y.ref))).getD x 0 := by
    intro x
    rw [toModule_evalWith, getD_toList]
    congr 1
    simp only [State.toModule, Ctx.mealy_outputs, Bundle.ports, refs, Array.toList_map, Array.toList_zip,
      List.map_map]
    rw [← HVec.toList_map_ref t ⟨env, store, ins, rst⟩]
    have hfun : ((fun o : OutPort => t.val ⟨env, store, ins, rst⟩ o.node) ∘
        fun p : Port × Nat => (⟨p.1.name, p.2⟩ : OutPort)) = t.val ⟨env, store, ins, rst⟩ ∘ Prod.snd := rfl
    rw [hfun, ← List.map_map, List.map_snd_zip (by simp [Bundle.widths])]
  have := decode_outputs t ⟨env, store, ins, rst⟩ (Bundle.toVec st.out)
    (fun e => Bundle.toVec (specO e)) [] ho
  simp only [List.length_nil, List.nil_append] at this
  unfold Bundle.decode
  simp only [hl]
  rw [this, Bundle.ofVec_toVec]

/-- Next registers of a finished Mealy module, decoded into the register record. -/
theorem mealy_regs (t : State (Ctx.mealy name I O R resets mems subs)) (st : Step O R)
    (specR : Env → R BitVec) (hn : BRefines t st.next specR) (env store ins rst) :
    Bundle.decode R (((t.toModule ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩).evalWith
      env store ins rst).2.regs.getD · 0) = Bundle.reset rst resets (specR ⟨env, store, ins, rst⟩) := by
  have hl : ∀ x, (((t.toModule ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩).evalWith
      env store ins rst).2.regs.getD x 0) =
      ((((Bundle.fields R).zip ((Bundle.toVec resets).toList fun r => r)).zip ((Bundle.toVec st.next).toList Sig.ref)).map
        fun p => Reg.update rst (t.val ⟨env, store, ins, rst⟩) ⟨Ident.ofString p.1.1.1, p.1.1.2, p.1.2, p.2⟩).getD x 0 := by
    intro x
    rw [toModule_evalWith, getD_toList]
    congr 1
    simp only [State.toModule, Ctx.mealy_regs, refs, Store.regs_mk, Array.toList_map, Array.toList_zip,
      List.map_map, List.zip_map_left]
    rfl
  have := decode_regs t ⟨env, store, ins, rst⟩ rst (Bundle.fields R) (Bundle.toVec resets)
    (Bundle.toVec st.next) (fun e => Bundle.toVec (specR e)) [] hn
  simp only [List.length_nil, List.nil_append] at this
  unfold Bundle.decode Bundle.reset
  simp only [hl]
  rw [this]

theorem HRefines.widths {t : State c} :
    ∀ {ws : List Nat} {v : HVec Sig ws} {f}, HRefines t v f →
      ∀ (k n : Nat), (v.toList Sig.ref)[k]? = some n → t.widths[n]? = ws[k]?
  | [], .nil, _, _, k, n, h => by simp [HVec.toList] at h
  | _ :: _, .cons x xs, _, h, k, n, hk => by
    cases k with
    | zero => simp [HVec.toList] at hk; subst hk; simpa using h.1.1
    | succ k => simpa using HRefines.widths h.2 k n (by simpa [HVec.toList] using hk)

/-- The wiring of a proved Mealy body is well-typed. -/
theorem mealy_wired (t : State (Ctx.mealy name I O R resets mems subs)) (st : Step O R)
    {specO : Env → O BitVec} {specR : Env → R BitVec}
    (ho : BRefines t st.out specO) (hn : BRefines t st.next specR)
    (hsize : st.writes.size = mems.size) (hports : ∀ (i : Nat) (ps : Array WritePort) (m : MemSpec),
      st.writes[i]? = some ps → mems[i]? = some m → ps.size = m.ports ∧
      ∀ p ∈ ps, t.widths[p.en]? = some 1 ∧ t.widths[p.addr]? = some m.addrWidth ∧ t.widths[p.data]? = some m.width) :
    Wired t ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Wiring.fits, refs, Bool.and_eq_true, beq_iff_eq, List.size_toArray, HVec.toList_length]
    refine ⟨⟨⟨?_, ?_⟩, hsize⟩, ?_⟩
    · simp [Bundle.ports, Bundle.widths]
    · simp [Bundle.widths]
    · rw [Array.all_eq_true]
      intro i hi
      have h1 : i < mems.size := (Nat.lt_min.mp (by simpa using hi)).1
      have h2 : i < st.writes.size := by omega
      have := (hports i st.writes[i] mems[i] (Array.getElem?_eq_getElem h2) (Array.getElem?_eq_getElem h1)).1
      simp [this]
  · intro k n hk
    have := HRefines.widths ho k n (by simpa [refs] using hk)
    rw [this]; simp [Bundle.ports, Bundle.widths]; rfl
  · intro k n hk
    have := HRefines.widths hn k n (by simpa [refs] using hk)
    rw [this]
    simp only [Ctx.mealy_regs, Array.getElem?_map, List.getElem?_toArray]
    rw [List.getElem?_map, Option.map_map]
    rw [show ∀ (l : List ((String × Nat) × Reset)), Option.map (RegSpec.width ∘
        fun p => (⟨Ident.ofString p.1.1, p.1.2, p.2⟩ : RegSpec)) l[k]? = (l.map (Prod.snd ∘ Prod.fst))[k]? from
        fun l => by rw [List.getElem?_map]; rfl]
    rw [← List.map_map, List.map_fst_zip (by simp), List.getElem?_map]
  · intro i ps m hps hm
    exact (hports i ps m hps hm).2

theorem Ctx.mealy_input_widths (k : Nat) :
    ((Ctx.mealy name I O R resets mems subs).inputs[k]?).map Port.width = (Bundle.widths I)[k]? ∨
      (Bundle.widths I).length ≤ k := by
  left
  simp only [Ctx.mealy_inputs, Bundle.ports, List.getElem?_toArray, List.getElem?_map, Option.map_map]
  rfl

theorem Ctx.mealy_reg_widths (k : Nat) :
    ((Ctx.mealy name I O R resets mems subs).regs[k]?).map RegSpec.width = (Bundle.widths R)[k]? ∨
      (Bundle.widths R).length ≤ k := by
  left
  simp only [Ctx.mealy_regs, Array.getElem?_map, List.getElem?_toArray, List.getElem?_map, Option.map_map]
  rw [show ∀ (l : List ((String × Nat) × Reset)), Option.map (RegSpec.width ∘
      fun p => (⟨Ident.ofString p.1.1, p.1.2, p.2⟩ : RegSpec)) l[k]? = (l.map (Prod.snd ∘ Prod.fst))[k]? from
      fun l => by rw [List.getElem?_map]; rfl]
  rw [← List.map_map, List.map_fst_zip (by simp), List.getElem?_map]

theorem Ctx.mealy_ok_pos (hc : (Ctx.mealy name I O R resets mems subs).ok = true) :
    (∀ w ∈ Bundle.widths I, 0 < w) ∧ (∀ w ∈ Bundle.widths R, 0 < w) := by
  simp only [Ctx.ok, Bool.and_eq_true, List.all_eq_true, Array.mem_toList_iff] at hc
  obtain ⟨⟨⟨hi, -⟩, hr⟩, -⟩ := hc
  constructor
  · intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    have hmem : (⟨Ident.ofString p.1, p.2⟩ : Port) ∈ (Ctx.mealy name I O R resets mems subs).inputs := by
      rw [Ctx.mealy_inputs, Bundle.ports, List.mem_toArray, List.mem_map]
      exact ⟨p, hp, rfl⟩
    simpa using hi _ hmem
  · intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    obtain ⟨i, hi', hpi⟩ := List.getElem_of_mem hp
    have hlen : i < ((Bundle.toVec resets).toList fun r => r).length := by simpa [Bundle.widths] using hi'
    have hmem : (⟨Ident.ofString p.1, p.2, ((Bundle.toVec resets).toList fun r => r)[i]⟩ : RegSpec) ∈
        (Ctx.mealy name I O R resets mems subs).regs := by
      simp only [Ctx.mealy_regs, Array.mem_map, List.mem_toArray]
      exact ⟨(p, _), by rw [← hpi]; exact List.mem_iff_getElem.mpr ⟨i, by simp [hi', hlen], by simp⟩, rfl⟩
    have := hr _ hmem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1

/-- The module built by a program, or the empty module if construction fails. -/
def Ctx.module (c : Ctx) (program : M c Wiring) : Module := (run c program).getD default

theorem Ctx.module_eq {c : Ctx} {program : M c Wiring} {r : Wiring} {t : State c}
    (hp : program (init c) = .ok (r, t)) (hc : c.ok = true) (hw : Wired t r) :
    c.module program = t.toModule r := by
  simp [Ctx.module, run_eq program r t hp hc hw]

/-- Memory write ports are wired to cells of the declared widths. -/
def WritesOk (t : State c) (ws : Array (Array WritePort)) (mems : Array MemSpec) : Prop :=
  ws.size = mems.size ∧ ∀ (i : Nat) (ps : Array WritePort) (m : MemSpec),
    ws[i]? = some ps → mems[i]? = some m → ps.size = m.ports ∧
    ∀ p ∈ ps, t.widths[p.en]? = some 1 ∧ t.widths[p.addr]? = some m.addrWidth ∧ t.widths[p.data]? = some m.width

theorem WritesOk.mono {s t : State c} {ws : Array (Array WritePort)} {mems : Array MemSpec}
    (h : WritesOk s ws mems) (hx : Extends s t) : WritesOk t ws mems :=
  ⟨h.1, fun i ps m h1 h2 =>
    have q := h.2 i ps m h1 h2
    ⟨q.1, fun p hp =>
      have r := q.2 p hp
      ⟨hx.widths r.1, hx.widths r.2.1, hx.widths r.2.2⟩⟩⟩

theorem WritesOk.nil {t : State c} : WritesOk t #[] #[] := ⟨rfl, fun _ _ _ h => by simp at h⟩

/-- Build a Mealy module from a proved body. The result exposes the final
builder state, so memories and instances can be reasoned about through it. -/
theorem mealy_build (hc : (Ctx.mealy name I O R resets mems subs).ok = true)
    (body : I Sig → R Sig → M (Ctx.mealy name I O R resets mems subs) (Step O R))
    (specO : Env → O BitVec) (specR : Env → R BitVec)
    (hbody : ∀ s ins regs, BRefines s ins (fun e => Bundle.decode I (e.ins.getD · 0)) →
      BRefines s regs (fun e => Bundle.decode R (e.st.regs.getD · 0)) →
      Ensures s (body ins regs) (fun st t => BRefines t st.out specO ∧ BRefines t st.next specR ∧
        WritesOk t st.writes mems)) :
    ∃ (t : State (Ctx.mealy name I O R resets mems subs)) (st : Step O R),
      (Ctx.mealy name I O R resets mems subs).module (mealy I O R body) =
        t.toModule ⟨refs (Bundle.toVec st.out), refs (Bundle.toVec st.next), st.writes⟩ ∧
      BRefines t st.out specO ∧ BRefines t st.next specR ∧ WritesOk t st.writes mems := by
  obtain ⟨hpI, hpR⟩ := Ctx.mealy_ok_pos hc
  obtain ⟨r, t, hp, -, st, hpost, rfl⟩ := mealy_ensures I O R body _
    Ctx.mealy_input_widths Ctx.mealy_reg_widths hpI hpR hbody
  exact ⟨t, st, Ctx.module_eq hp hc (mealy_wired t st hpost.1 hpost.2.1 hpost.2.2.1 hpost.2.2.2),
    hpost.1, hpost.2.1, hpost.2.2⟩

end

end HDLean.Rtl.Build
