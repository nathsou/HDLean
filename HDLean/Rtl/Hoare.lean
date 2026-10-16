import HDLean.Rtl.Build

/-!
# Specifications for builder programs

`Refines s x f` says that, in every cycle environment `e`, handle `x` of state
`s` carries the bit-vector `f e`. `Ensures s m post` is a Hoare triple for the
builder program `m` started in `s`. Every primitive has an `*_ensures` lemma,
and all specifications survive further allocation (`Refines.mono`).
-/
namespace HDLean.Rtl.Build

/-- One cycle of one module instance, seen from inside the module. -/
structure Env where
  sem : Nat → Sem
  st : Store
  ins : Array Nat
  rst : Bool

def evalCells (e : Env) (cells : Array Cell) : Acc :=
  cells.foldl (stepCell e.sem e.st e.ins e.rst) ⟨#[], #[]⟩

def State.val (s : State c) (e : Env) (k : Nat) : Nat := (evalCells e s.cells).vals.getD k 0

@[simp] theorem bv_toNat (x : BitVec w) : bv w x.toNat = x := by simp [bv]
@[simp] theorem bv_mod (w v : Nat) : bv w (v % 2 ^ w) = bv w v := by
  apply BitVec.eq_of_toNat_eq; simp [bv]

/-! ## Evaluation is a prefix computation -/

theorem stepCell_size (env st ins rst) (acc : Acc) (c : Cell) :
    (stepCell env st ins rst acc c).vals.size = acc.vals.size + 1 := by
  unfold stepCell; split <;> simp

theorem stepCell_prefix (env st ins rst) (acc : Acc) (c : Cell) (k : Nat) (hk : k < acc.vals.size) :
    (stepCell env st ins rst acc c).vals.getD k 0 = acc.vals.getD k 0 := by
  unfold stepCell
  split <;> simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt hk]

theorem foldl_size (env st ins rst) (cs : List Cell) (acc : Acc) :
    (cs.foldl (stepCell env st ins rst) acc).vals.size = acc.vals.size + cs.length := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih => simp only [List.foldl_cons, ih, stepCell_size, List.length_cons]; omega

theorem foldl_prefix (env st ins rst) (cs : List Cell) (acc : Acc) (k : Nat) (hk : k < acc.vals.size) :
    (cs.foldl (stepCell env st ins rst) acc).vals.getD k 0 = acc.vals.getD k 0 := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by rw [stepCell_size]; omega), stepCell_prefix _ _ _ _ _ _ _ hk]

@[simp] theorem evalCells_size (e : Env) (cells : Array Cell) :
    (evalCells e cells).vals.size = cells.size := by
  simp [evalCells, ← Array.foldl_toList, foldl_size]

theorem evalCells_push (e : Env) (cells : Array Cell) (c : Cell) :
    evalCells e (cells.push c) = stepCell e.sem e.st e.ins e.rst (evalCells e cells) c := by
  simp [evalCells, Array.foldl_push]

theorem evalCells_append (e : Env) (cells more : Array Cell) (k : Nat) (hk : k < cells.size) :
    (evalCells e (cells ++ more)).vals.getD k 0 = (evalCells e cells).vals.getD k 0 := by
  have hs := evalCells_size e cells
  unfold evalCells at hs ⊢
  rw [Array.foldl_append, ← Array.foldl_toList (xs := more)]
  exact foldl_prefix _ _ _ _ _ _ _ (by omega)

/-- The value of a freshly allocated non-instance cell. -/
theorem val_push (e : Env) (cells : Array Cell) (w : Nat) (op : Op)
    (hop : ∀ j args outs, op ≠ .inst j args outs) :
    (evalCells e (cells.push ⟨w, op⟩)).vals.getD cells.size 0 =
      (op.evalBV (frame e.st e.ins (evalCells e cells).vals) w).toNat := by
  rw [evalCells_push]
  unfold stepCell
  split
  · rename_i j args outs h; exact absurd h (hop j args outs)
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, if_pos (by simp)]; rfl

/-! ## Specifications -/

/-- Handle `x` carries `f e` in every environment `e`. -/
def Refines (s : State c) (x : Sig w) (f : Env → BitVec w) : Prop :=
  s.widths[x.ref]? = some w ∧ ∀ e, s.val e x.ref = (f e).toNat

theorem Refines.lt {s : State c} {x : Sig w} {f} (h : Refines s x f) : x.ref < s.cells.size := by
  have h1 := h.1
  rw [s.widths_eq] at h1
  rcases Nat.lt_or_ge x.ref s.cells.size with hl | hl
  · exact hl
  · simp [Array.getElem?_eq_none (by simpa using hl)] at h1

theorem Refines.bv {s : State c} {x : Sig w} {f} (h : Refines s x f) (e : Env) :
    bv w (s.val e x.ref) = f e := by rw [h.2 e]; simp

/-- Later states keep every cell. -/
def Extends (s t : State c) : Prop := ∃ more, t.cells = s.cells ++ more

theorem Extends.refl (s : State c) : Extends s s := ⟨#[], by simp⟩

theorem Extends.trans {s t u : State c} (h : Extends s t) (h' : Extends t u) : Extends s u := by
  obtain ⟨a, ha⟩ := h; obtain ⟨b, hb⟩ := h'
  exact ⟨a ++ b, by rw [hb, ha, Array.append_assoc]⟩

theorem Extends.widths {s t : State c} (h : Extends s t) {k v : Nat} (hk : s.widths[k]? = some v) :
    t.widths[k]? = some v := by
  obtain ⟨more, hm⟩ := h
  rw [t.widths_eq, hm, Array.map_append]
  rw [s.widths_eq] at hk
  have hlt : k < (s.cells.map Cell.width).size := by
    rcases Nat.lt_or_ge k (s.cells.map Cell.width).size with hl | hl
    · exact hl
    · simp [Array.getElem?_eq_none hl] at hk
  rw [Array.getElem?_append_left hlt, hk]

theorem Extends.val {s t : State c} (h : Extends s t) (e : Env) {k : Nat} (hk : k < s.cells.size) :
    t.val e k = s.val e k := by
  obtain ⟨more, hm⟩ := h
  unfold State.val
  rw [hm]
  exact evalCells_append e s.cells more k hk

theorem Refines.mono {s t : State c} {x : Sig w} {f} (h : Refines s x f) (hx : Extends s t) :
    Refines t x f :=
  ⟨hx.widths h.1, fun e => (hx.val e h.lt).trans (h.2 e)⟩

def Ensures (s : State c) (m : M c α) (post : α → State c → Prop) : Prop :=
  ∃ a t, m s = some (a, t) ∧ Extends s t ∧ post a t

theorem ensures_pure (s : State c) (a : α) {post : α → State c → Prop} (h : post a s) :
    Ensures s (pure a) post := ⟨a, s, rfl, Extends.refl s, h⟩

theorem ensures_bind {s : State c} {m : M c α} {f : α → M c β} {p : α → State c → Prop}
    {q : β → State c → Prop} (h : Ensures s m p)
    (k : ∀ a t, Extends s t → p a t → Ensures t (f a) q) : Ensures s (m >>= f) q := by
  obtain ⟨a, t, hm, he, hp⟩ := h
  obtain ⟨b, u, hf, he', hq⟩ := k a t he hp
  exact ⟨b, u, by simp [bind, StateT.bind, hm, hf], he.trans he', hq⟩

theorem ensures_weaken {s : State c} {m : M c α} {p q : α → State c → Prop} (h : Ensures s m p)
    (hp : ∀ a t, p a t → q a t) : Ensures s m q := by
  obtain ⟨a, t, hm, he, h⟩ := h
  exact ⟨a, t, hm, he, hp a t h⟩

/-- Postconditions may mention the starting state through monotone facts. -/
theorem ensures_frame {s : State c} {m : M c α} {p : α → State c → Prop} (h : Ensures s m p) :
    Ensures s m (fun a t => Extends s t ∧ p a t) := by
  obtain ⟨a, t, hm, he, hp⟩ := h
  exact ⟨a, t, hm, he, he, hp⟩

/-! ## Primitive lemmas -/

theorem emit_ensures (s : State c) (w : Nat) (op : Op) (hop : ∀ j args outs, op ≠ .inst j args outs)
    (hv : (0 < w && op.valid c.scope s.widths w) = true) :
    Ensures s (emit w op) (fun x t => t.widths[x.ref]? = some w ∧
      ∀ e, t.val e x.ref = (op.evalBV (frame e.st e.ins (evalCells e s.cells).vals) w).toNat) := by
  refine ⟨⟨s.cells.size⟩, _, by simp [emit, hv]; rfl, ?_, ?_⟩
  · exact ⟨#[⟨w, op⟩], by simp⟩
  · refine ⟨?_, fun e => ?_⟩
    · show (s.widths.push w)[s.cells.size]? = some w
      rw [Array.getElem?_push, if_pos (by simp [s.widths_eq])]
    · exact val_push e s.cells w op hop

/-- Frame of an environment, read through a state. -/
theorem frame_val (s : State c) (e : Env) (k : Nat) :
    (frame e.st e.ins (evalCells e s.cells).vals).val k = s.val e k := rfl

theorem const_ensures (s : State c) (w : Nat) (v : BitVec w) (hw : 0 < w) :
    Ensures s (const w v) (fun x t => Refines t x (fun _ => v)) := by
  apply ensures_weaken (emit_ensures s w (.const v.toNat) (by intros; simp) (by simp [Op.valid, hw, v.isLt]))
  intro x t ⟨hw, hv⟩
  exact ⟨hw, fun e => by rw [hv]; simp [Op.evalBV]⟩

theorem input_ensures (s : State c) (k w : Nat) (hw : 0 < w)
    (hk : (c.inputs[k]?).map Port.width = some w) :
    Ensures s (input k w) (fun x t => Refines t x (fun e => bv w (e.ins.getD k 0))) := by
  apply ensures_weaken (emit_ensures s w (.input k) (by intros; simp)
    (by simp [Op.valid, hw, Ctx.scope, Array.getElem?_map, hk]))
  intro x t ⟨hw, hv⟩
  exact ⟨hw, fun e => by rw [hv]; rfl⟩

theorem not_ensures {s : State c} {a : Sig w} {fa} (ha : Refines s a fa) (hw : 0 < w) :
    Ensures s (not a) (fun x t => Refines t x (fun e => ~~~(fa e))) := by
  apply ensures_weaken (emit_ensures s w (.not a.ref) (by intros; simp) (by simp [Op.valid, hw, ha.1]))
  intro x t ⟨hw, hv⟩
  exact ⟨hw, fun e => by rw [hv]; simp only [Op.evalBV, frame_val, ha.bv e]⟩

theorem neg_ensures {s : State c} {a : Sig w} {fa} (ha : Refines s a fa) (hw : 0 < w) :
    Ensures s (neg a) (fun x t => Refines t x (fun e => -(fa e))) := by
  apply ensures_weaken (emit_ensures s w (.neg a.ref) (by intros; simp) (by simp [Op.valid, hw, ha.1]))
  intro x t ⟨hw, hv⟩
  exact ⟨hw, fun e => by rw [hv]; simp only [Op.evalBV, frame_val, ha.bv e]⟩

theorem bin_ensures {s : State c} {a b : Sig w} {fa fb} (op : BinOp) (ha : Refines s a fa)
    (hb : Refines s b fb) (hw : 0 < w) :
    Ensures s (bin op a b) (fun x t => Refines t x (fun e => op.eval (fa e) (fb e) (fb e).toNat)) := by
  apply ensures_weaken (emit_ensures s w (.bin op a.ref b.ref) (by intros; simp)
    (by cases op <;> simp [Op.valid, hw, ha.1, hb.1, BinOp.isShift]))
  intro x t ⟨hw, hv⟩
  exact ⟨hw, fun e => by rw [hv]; simp only [Op.evalBV, frame_val, ha.bv e, hb.bv e, hb.2 e, bv_toNat]⟩

theorem shift_ensures {s : State c} {a : Sig w} {b : Sig v} {fa fb} (op : BinOp) (hs : op.isShift = true)
    (ha : Refines s a fa) (hb : Refines s b fb) (hw : 0 < w) :
    Ensures s (shift op a b) (fun x t => Refines t x (fun e => op.eval (fa e) (bv w (fb e).toNat) (fb e).toNat)) := by
  apply ensures_weaken (emit_ensures s w (.bin op a.ref b.ref) (by intros; simp)
    (by simp [Op.valid, hw, ha.1, hb.1, hs]))
  intro x t ⟨hw, hv⟩
  exact ⟨hw, fun e => by rw [hv]; simp only [Op.evalBV, frame_val, ha.bv e, hb.2 e, bv_toNat]⟩

theorem cmp_ensures {s : State c} {a b : Sig w} {fa fb} (op : CmpOp) (ha : Refines s a fa)
    (hb : Refines s b fb) :
    Ensures s (cmp op a b) (fun x t => Refines t x (fun e => BitVec.ofBool (op.eval (fa e) (fb e)))) := by
  apply ensures_weaken (emit_ensures s 1 (.cmp op w a.ref b.ref) (by intros; simp)
    (by simp [Op.valid, ha.1, hb.1]))
  intro x t ⟨hw, hv⟩
  exact ⟨hw, fun e => by rw [hv]; simp only [Op.evalBV, frame_val, ha.bv e, hb.bv e, BitVec.setWidth_eq]⟩

theorem mux_ensures {s : State c} {sel : Sig 1} {a b : Sig w} {fs fa fb} (hs : Refines s sel fs)
    (ha : Refines s a fa) (hb : Refines s b fb) (hw : 0 < w) :
    Ensures s (mux sel a b) (fun x t => Refines t x (fun e => if (fs e).getLsbD 0 then fa e else fb e)) := by
  apply ensures_weaken (emit_ensures s w (.mux sel.ref a.ref b.ref) (by intros; simp)
    (by simp [Op.valid, hw, ha.1, hb.1, hs.1]))
  intro x t ⟨hw, hv⟩
  refine ⟨hw, fun e => ?_⟩
  rw [hv]
  simp only [Op.evalBV, frame_val, ha.bv e, hb.bv e, hs.2 e, BitVec.getLsbD]

theorem slice_ensures {s : State c} {a : Sig v} {fa} (lo w : Nat) (ha : Refines s a fa) (hw : 0 < w)
    (hr : lo + w ≤ v) :
    Ensures s (slice a lo w) (fun x t => Refines t x (fun e => (fa e).extractLsb' lo w)) := by
  apply ensures_weaken (emit_ensures s w (.slice a.ref lo) (by intros; simp)
    (by simp [Op.valid, hw, ha.1, hr]))
  intro x t ⟨hw, hv⟩
  exact ⟨hw, fun e => by rw [hv]; simp only [Op.evalBV, frame_val, ha.2 e]; rfl⟩

theorem concat_ensures {s : State c} {h : Sig v} {l : Sig u} {fh fl} (hh : Refines s h fh)
    (hl : Refines s l fl) (hw : 0 < v + u) :
    Ensures s (concat h l) (fun x t => Refines t x (fun e => fh e ++ fl e)) := by
  apply ensures_weaken (emit_ensures s (v + u) (.concat h.ref l.ref u) (by intros; simp)
    (by simp [Op.valid, hw, hh.1, hl.1]))
  intro x t ⟨hw, hv⟩
  refine ⟨hw, fun e => ?_⟩
  rw [hv]
  congr 1
  simp only [Op.evalBV, frame_val, hh.2 e, hl.2 e]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  split
  · simp
  · simp only [bv, BitVec.getLsbD_ofNat, Nat.add_sub_cancel]
    rw [← BitVec.getLsbD]
    simp [show i - u < v by omega]

theorem zext_ensures {s : State c} {a : Sig v} {fa} (w : Nat) (ha : Refines s a fa) (hw : 0 < w)
    (hr : v ≤ w) :
    Ensures s (zext a w) (fun x t => Refines t x (fun e => (fa e).setWidth w)) := by
  apply ensures_weaken (emit_ensures s w (.zext a.ref) (by intros; simp)
    (by simp [Op.valid, hw, ha.1, hr]))
  intro x t ⟨hw, hv⟩
  exact ⟨hw, fun e => by rw [hv]; simp only [Op.evalBV, frame_val, ha.2 e, bv, BitVec.ofNat_toNat]⟩

theorem sext_ensures {s : State c} {a : Sig v} {fa} (w : Nat) (ha : Refines s a fa) (hw : 0 < w)
    (hr : v ≤ w) :
    Ensures s (sext a w) (fun x t => Refines t x (fun e => (fa e).signExtend w)) := by
  apply ensures_weaken (emit_ensures s w (.sext a.ref v) (by intros; simp)
    (by simp [Op.valid, hw, ha.1, hr]))
  intro x t ⟨hw, hv⟩
  exact ⟨hw, fun e => by rw [hv]; simp only [Op.evalBV, frame_val, ha.bv e]⟩

theorem regRead_ensures (s : State c) (k w : Nat) (hw : 0 < w)
    (hk : (c.regs[k]?).map RegSpec.width = some w) :
    Ensures s (regRead k w) (fun x t => Refines t x (fun e => bv w (e.st.regs.getD k 0))) := by
  apply ensures_weaken (emit_ensures s w (.reg k) (by intros; simp)
    (by simp [Op.valid, hw, Ctx.scope, Array.getElem?_map, hk]))
  intro x t ⟨hw, hv⟩
  exact ⟨hw, fun e => by rw [hv]; rfl⟩

theorem memRead_ensures {s : State c} (k w : Nat) {a : Sig aw} {fa} (ha : Refines s a fa) (hw : 0 < w)
    (hk : (c.mems[k]?).map (fun m => (m.addrWidth, m.width)) = some (aw, w)) :
    Ensures s (memRead k w a)
      (fun x t => Refines t x (fun e => bv w ((e.st.mems.getD k #[]).getD (fa e).toNat 0))) := by
  have hk' : (c.scope.mems)[k]? = some (aw, w) := by simpa [Ctx.scope, Array.getElem?_map] using hk
  apply ensures_weaken (emit_ensures s w (.memRead k a.ref) (by intros; simp)
    (by simp [Op.valid, hw, hk', ha.1]))
  intro x t ⟨hw, hv⟩
  exact ⟨hw, fun e => by rw [hv]; simp only [Op.evalBV, frame_val, ha.2 e]; rfl⟩

/-- Number of instance cells; the next instance owns this store slot. -/
def slots (cells : Array Cell) : Nat :=
  cells.toList.countP fun c => match c.op with | .inst .. => true | _ => false

theorem stepCell_subs (env st ins rst) (acc : Acc) (c : Cell) :
    (stepCell env st ins rst acc c).subs.size =
      acc.subs.size + (match c.op with | .inst .. => 1 | _ => 0) := by
  unfold stepCell
  split <;> rename_i h <;> simp [h]

theorem evalCells_subs_size (e : Env) (cells : Array Cell) : (evalCells e cells).subs.size = slots cells := by
  unfold evalCells slots
  rw [← Array.foldl_toList]
  suffices ∀ (l : List Cell) (acc : Acc), (l.foldl (stepCell e.sem e.st e.ins e.rst) acc).subs.size =
      acc.subs.size + l.countP (fun c => match c.op with | .inst .. => true | _ => false) by
    simpa using this cells.toList ⟨#[], #[]⟩
  intro l
  induction l with
  | nil => simp
  | cons c l ih =>
    intro acc
    simp only [List.foldl_cons, ih, stepCell_subs, List.countP_cons]
    split <;> rename_i h <;> simp [h] <;> omega

/-- An instance of module `j`: its value is the packed outputs of `env j` on the
instance's own store slot. -/
theorem inst_ensures (s : State c) (j : Nat) (args outs : List Nat) (hw : 0 < outs.sum)
    (hv : (Op.inst j args outs).valid c.scope s.widths outs.sum = true) :
    Ensures s (inst j args outs) (fun x t => t.widths[x.ref]? = some outs.sum ∧ ∀ e, t.val e x.ref =
      (bv outs.sum (pack outs (e.sem j (e.st.subs.getD (slots s.cells) default)
        (args.toArray.map (s.val e ·)) e.rst).1.toList)).toNat) := by
  refine ⟨⟨s.cells.size⟩, _, by simp [inst, emit, hv, hw]; rfl, ⟨#[⟨outs.sum, .inst j args outs⟩], by simp⟩, ?_⟩
  refine ⟨?_, fun e => ?_⟩
  · show (s.widths.push outs.sum)[s.cells.size]? = some outs.sum
    rw [Array.getElem?_push, if_pos (by simp [s.widths_eq])]
  · show (evalCells e (s.cells.push ⟨outs.sum, .inst j args outs⟩)).vals.getD s.cells.size 0 = _
    rw [evalCells_push]
    simp only [stepCell, evalCells_subs_size]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, if_pos (by simp)]
    rfl

/-- The next store of an instance created in state `s`. -/
theorem inst_sub (s t : State c) (j : Nat) (args outs : List Nat) (w : Nat)
    (ht : ∃ more, t.cells = (s.cells.push ⟨w, .inst j args outs⟩) ++ more) (e : Env) :
    (evalCells e t.cells).subs[slots s.cells]? =
      some (e.sem j (e.st.subs.getD (slots s.cells) default) (args.toArray.map (s.val e ·)) e.rst).2 := by
  obtain ⟨more, hm⟩ := ht
  rw [hm]
  unfold evalCells
  rw [Array.foldl_append, ← Array.foldl_toList (xs := more)]
  have hpre : ∀ (l : List Cell) (acc : Acc) (k : Nat), k < acc.subs.size →
      (l.foldl (stepCell e.sem e.st e.ins e.rst) acc).subs[k]? = acc.subs[k]? := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons c l ih =>
      intro acc k hk
      simp only [List.foldl_cons]
      rw [ih _ _ (by rw [stepCell_subs]; omega)]
      unfold stepCell
      split <;> simp [Array.getElem?_push, Nat.ne_of_lt hk]
  have hs := evalCells_subs_size e s.cells
  unfold evalCells at hs
  rw [hpre _ _ _ (by rw [Array.foldl_push, stepCell_subs]; simp [hs])]
  rw [Array.foldl_push]
  simp only [stepCell]
  rw [Array.getElem?_push, if_pos hs.symm, hs]
  rfl

/-! ## Finishing -/

/-- The wiring returned by a program has the declared shape and widths. -/
def Wired (t : State c) (r : Wiring) : Prop :=
  r.fits c = true ∧
  (∀ (k n : Nat), r.outputs[k]? = some n → t.widths[n]? = (c.outputs[k]?).map Port.width) ∧
  (∀ (k n : Nat), r.nexts[k]? = some n → t.widths[n]? = (c.regs[k]?).map RegSpec.width) ∧
  (∀ (i : Nat) (ps : Array WritePort) (m : MemSpec), r.writes[i]? = some ps → c.mems[i]? = some m →
    ∀ p ∈ ps, t.widths[p.en]? = some 1 ∧ t.widths[p.addr]? = some m.addrWidth ∧ t.widths[p.data]? = some m.width)

theorem toModule_check (t : State c) (r : Wiring) (hc : c.ok = true) (hw : Wired t r) :
    (t.toModule r).check c.subs = true := by
  obtain ⟨hfit, hout, hnext, hwr⟩ := hw
  simp only [Wiring.fits, Bool.and_eq_true, beq_iff_eq] at hfit
  obtain ⟨⟨⟨ho, hn⟩, hm⟩, hports⟩ := hfit
  simp only [Ctx.ok, Bool.and_eq_true, List.all_eq_true, Array.mem_toList_iff] at hc
  obtain ⟨⟨⟨hci, hco⟩, hcr⟩, hcm⟩ := hc
  have hwid : ∀ k : Nat, (t.toModule r).cells[k]?.map Cell.width = t.widths[k]? := by
    intro k; simp [State.toModule, t.widths_eq, Array.getElem?_map]
  have hscope : (t.toModule r).scope c.subs = c.scope := by
    simp only [Module.scope, Ctx.scope, State.toModule]
    congr 1
    · apply Array.ext
      · simp [hn]
      · intro i h1 h2; simp
    · apply Array.ext
      · simp [hm]
      · intro i h1 h2; simp
  have h1 : (t.toModule r).inputs.all (fun p => 0 < p.width) = true := by
    show c.inputs.all _ = true
    rw [Array.all_eq_true]; intro i hi; exact hci _ (Array.getElem_mem hi)
  have h2 : cellsValid ((t.toModule r).scope c.subs) (t.toModule r).cells = true := by
    rw [hscope]; exact t.valid
  have h3 : (t.toModule r).regs.all (fun x => 0 < x.width &&
      (t.toModule r).cells[x.next]?.map Cell.width == some x.width &&
      match x.reset with | .none => true | .sync v => decide (v < 2 ^ x.width)) = true := by
    rw [Array.all_eq_true]
    intro i hi
    have hi1 : i < c.regs.size := by simpa [State.toModule, hn] using hi
    have hi2 : i < r.nexts.size := by omega
    have e : (t.toModule r).regs[i] = ⟨c.regs[i].name, c.regs[i].width, c.regs[i].reset, r.nexts[i]⟩ := by
      simp [State.toModule]
    rw [e, hwid, hnext i r.nexts[i] (Array.getElem?_eq_getElem hi2), Array.getElem?_eq_getElem hi1]
    have := hcr _ (Array.getElem_mem hi1)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    simp only [Option.map_some, beq_self_eq_true, Bool.and_true, decide_eq_true this.1, Bool.true_and]
    have hf := this.2
    revert hf
    cases c.regs[i].reset <;> simp [Reset.fits]
  have h4 : (t.toModule r).mems.all (fun mm => 0 < mm.addrWidth && 0 < mm.width && mm.writes.all fun p =>
      (t.toModule r).cells[p.en]?.map Cell.width == some 1 &&
      (t.toModule r).cells[p.addr]?.map Cell.width == some mm.addrWidth &&
      (t.toModule r).cells[p.data]?.map Cell.width == some mm.width) = true := by
    rw [Array.all_eq_true]
    intro i hi
    have hi1 : i < c.mems.size := by simpa [State.toModule, hm] using hi
    have hi2 : i < r.writes.size := by omega
    have e : (t.toModule r).mems[i] = ⟨c.mems[i].name, c.mems[i].addrWidth, c.mems[i].width, r.writes[i]⟩ := by
      simp [State.toModule]
    rw [e]
    have := hcm _ (Array.getElem_mem hi1)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨decide_eq_true this.1, decide_eq_true this.2⟩, ?_⟩
    rw [Array.all_eq_true]
    intro k hk
    have := hwr i r.writes[i] c.mems[i] (Array.getElem?_eq_getElem hi2) (Array.getElem?_eq_getElem hi1)
      r.writes[i][k] (Array.getElem_mem hk)
    simp [hwid, this.1, this.2.1, this.2.2]
  have h5 : (t.toModule r).outputs.all (fun o => ((t.toModule r).cells[o.node]?.map Cell.width).isSome) = true := by
    rw [Array.all_eq_true]
    intro k hk
    have hk1 : k < c.outputs.size := by simpa [State.toModule, ho] using hk
    have hk2 : k < r.outputs.size := by omega
    have e : (t.toModule r).outputs[k].node = r.outputs[k] := by simp [State.toModule]
    rw [e, hwid, hout k r.outputs[k] (Array.getElem?_eq_getElem hk2), Array.getElem?_eq_getElem hk1]
    rfl
  simp only [Module.check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

/-- A program run whose wiring is well-typed yields exactly the module of its final state. -/
theorem run_eq {c : Ctx} (program : M c Wiring) (r : Wiring) (t : State c)
    (hp : program (init c) = some (r, t)) (hc : c.ok = true) (hw : Wired t r) :
    run c program = some (t.toModule r) := by
  have hcheck := toModule_check t r hc hw
  simp [run, hp, hc, hw.1, hcheck]

/-- The cycle semantics of a finished module, read through the builder state. -/
theorem toModule_evalWith (t : State c) (r : Wiring) (env : Nat → Sem)
    (st : Store) (ins : Array Nat) (rst : Bool) :
    (t.toModule r).evalWith env st ins rst =
      ((t.toModule r).outputs.map (fun o => t.val ⟨env, st, ins, rst⟩ o.node),
       Store.mk ((t.toModule r).regs.map (Reg.update rst (t.val ⟨env, st, ins, rst⟩)))
         ((t.toModule r).mems.mapIdx fun i mm => mm.update (t.val ⟨env, st, ins, rst⟩) (st.mems.getD i #[]))
         (evalCells ⟨env, st, ins, rst⟩ t.cells).subs) := rfl

end HDLean.Rtl.Build
