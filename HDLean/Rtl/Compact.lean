import HDLean.Rtl.Optimize

/-!
# Removing dead cells

`Design.compact` drops every non-instance cell that no output, register,
memory write port or kept cell reads, and renumbers the rest. Instance cells
are always kept (each owns a slot of the store), so registers, memories and
child stores keep their layout and every store means the same state.

Liveness is a hint: the pass checks that every kept cell's operands, every
output, register input and write port were kept, and returns the module
unchanged otherwise. `Design.compact_sem`: every module keeps its semantics.
-/
namespace HDLean.Rtl.Opt
open HDLean.Rtl.Build

set_option linter.unusedSimpArgs false

/-- Rename every cell reference of an operation. -/
def _root_.HDLean.Rtl.Op.mapArgs (f : Nat → Nat) : Op → Op
  | .const v => .const v
  | .input k => .input k
  | .reg k => .reg k
  | .memRead mi a => .memRead mi (f a)
  | .not a => .not (f a)
  | .neg a => .neg (f a)
  | .bin o a b => .bin o (f a) (f b)
  | .cmp o w a b => .cmp o w (f a) (f b)
  | .mux s a b => .mux (f s) (f a) (f b)
  | .slice a lo => .slice (f a) lo
  | .concat h l lw => .concat (f h) (f l) lw
  | .zext a => .zext (f a)
  | .sext a fw => .sext (f a) fw
  | .inst j args outs => .inst j (args.map f) outs

/-- Cells something reads (a hint). -/
def _root_.HDLean.Rtl.Module.liveCells (m : Module) : Array Bool := Id.run do
  let mut live := Array.replicate m.cells.size false
  for o in m.outputs do live := live.set! o.node true
  for r in m.regs do live := live.set! r.next true
  for mm in m.mems do
    for p in mm.writes do
      live := ((live.set! p.en true).set! p.addr true).set! p.data true
  for k in (List.range m.cells.size).reverse do
    if live[k]! || (m.cells[k]!.op.isInst) then
      for a in m.cells[k]!.op.args do live := live.set! a true
  return live

structure Cp where
  ren : Array (Option Nat)
  size : Nat
  ok : Bool

def Cp.f (s : Cp) (x : Nat) : Nat := ((s.ren[x]?).join).getD 0
def Cp.mapped (s : Cp) (x : Nat) : Bool := ((s.ren[x]?).join).isSome

/-- Keep or drop the next cell. -/
def Cp.step (live : Array Bool) (s : Cp) (c : Cell) : Cp × Option Cell :=
  if live.getD s.ren.size false || c.op.isInst then
    (⟨s.ren.push (some s.size), s.size + 1, s.ok && c.op.args.all s.mapped⟩, some ⟨c.width, c.op.mapArgs s.f⟩)
  else (⟨s.ren.push none, s.size, s.ok⟩, none)

def cpList (live : Array Bool) : Cp → List Cell → Cp × List Cell
  | s, [] => (s, [])
  | s, c :: cs =>
    let p := s.step live c
    let r := cpList live p.1 cs
    (r.1, p.2.toList ++ r.2)

/-- The module with the kept cells and renamed references. -/
def compactWith (m : Module) (s : Cp) (cells : List Cell) : Module :=
  { m with
    cells := cells.toArray
    outputs := m.outputs.map fun o => { o with node := s.f o.node }
    regs := m.regs.map fun reg => { reg with next := s.f reg.next }
    mems := m.mems.map fun mm => { mm with writes := mm.writes.map fun p => ⟨s.f p.en, s.f p.addr, s.f p.data⟩ } }

def refsOk (m : Module) (s : Cp) : Bool :=
  m.outputs.all (fun o => s.mapped o.node) && m.regs.all (fun reg => s.mapped reg.next) &&
    m.mems.all (fun mm => mm.writes.all fun p => s.mapped p.en && s.mapped p.addr && s.mapped p.data)

def _root_.HDLean.Rtl.Module.compact (m : Module) : Module :=
  let r := cpList m.liveCells ⟨#[], 0, true⟩ m.cells.toList
  if r.1.ok && refsOk m r.1 then compactWith m r.1 r.2 else m

def _root_.HDLean.Rtl.Design.compact (d : Design) : Design := ⟨d.modules.map Module.compact⟩

/-! ## Soundness -/

theorem evalBV_mapArgs (f : Nat → Nat) (fr fr' : Frame) (w : Nat) (op : Op)
    (hv : ∀ x ∈ op.args, fr'.val (f x) = fr.val x)
    (hi : fr'.input = fr.input) (hr : fr'.reg = fr.reg) (hm : fr'.mem = fr.mem) :
    (op.mapArgs f).evalBV fr' w = op.evalBV fr w := by
  cases op <;> simp only [Op.args, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hv <;>
    simp [Op.mapArgs, Op.evalBV, hi, hr, hm, hv]

theorem mapArgs_isInst (f : Nat → Nat) (op : Op) : (op.mapArgs f).isInst = op.isInst := by
  cases op <;> rfl

section
variable (env : Nat → Sem) (st : Store) (ins : Array Nat) (rst : Bool)

/-- The kept cells' new values are their old values. -/
def CpRel (s : Cp) (old new : Acc) : Prop :=
  s.ren.size = old.vals.size ∧ new.vals.size = s.size ∧ new.subs = old.subs ∧
    ∀ j t, (s.ren[j]?).join = some t → t < s.size ∧ new.vals.getD t 0 = old.vals.getD j 0

theorem CpRel.f_val {s : Cp} {old new : Acc} (h : CpRel s old new) (x : Nat) (hx : s.mapped x = true) :
    new.vals.getD (s.f x) 0 = old.vals.getD x 0 := by
  unfold Cp.mapped at hx
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hx
  simp only [Cp.f, ht, Option.getD_some]
  exact (h.2.2.2 x t ht).2

theorem getD_push_lt (a : Array Nat) (v j : Nat) (hj : j < a.size) : (a.push v).getD j 0 = a.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt hj]

theorem getD_push_eq (a : Array Nat) (v : Nat) : (a.push v).getD a.size 0 = v := by
  simp [Array.getD_eq_getD_getElem?]

theorem stepCell_noninst (acc : Acc) (w : Nat) (op : Op) (h : op.isInst = false) :
    stepCell env st ins rst acc ⟨w, op⟩ = ⟨acc.vals.push (op.evalBV (frame st ins acc.vals) w).toNat, acc.subs⟩ := by
  cases op <;> simp_all [Op.isInst, stepCell]

theorem foldl_congr_mem {l : List α} {f g : β → α → β} (h : ∀ a ∈ l, ∀ b, f b a = g b a) (init : β) :
    l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldl_cons]
    rw [h a (by simp)]
    exact ih (fun x hx => h x (by simp [hx])) _

theorem mem_update_rename (mm : Mem) (f : Nat → Nat) (v v' : Nat → Nat) (old : Array Nat)
    (h : ∀ p ∈ mm.writes.toList, v' (f p.en) = v p.en ∧ v' (f p.addr) = v p.addr ∧ v' (f p.data) = v p.data) :
    ({ mm with writes := mm.writes.map fun p => (⟨f p.en, f p.addr, f p.data⟩ : WritePort) } : Mem).update v' old =
      mm.update v old := by
  simp only [Mem.update, Mem.shape]
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map, List.foldl_map]
  apply foldl_congr_mem
  intro p hp arr
  obtain ⟨h1, h2, h3⟩ := h p hp
  simp only [h1, h2, h3]

theorem cpStep_sound (live : Array Bool) (s : Cp) (old new : Acc) (c : Cell) (h : CpRel s old new)
    (hok : (s.step live c).1.ok = true) :
    s.ok = true ∧ CpRel (s.step live c).1 (stepCell env st ins rst old c)
      ((s.step live c).2.toList.foldl (stepCell env st ins rst) new) := by
  have hsz := Build.stepCell_size env st ins rst old c
  unfold Cp.step at hok ⊢
  split
  · rename_i hkeep
    simp only [hkeep, ite_true, Bool.and_eq_true, List.all_eq_true] at hok
    obtain ⟨hsok, hargs⟩ := hok
    refine ⟨hsok, ?_⟩
    simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
    -- the new cell computes the old cell's value
    have hval : ∀ x ∈ c.op.args, (frame st ins new.vals).val (s.f x) = (frame st ins old.vals).val x :=
      fun x hx => h.f_val x (hargs x hx)
    have hnew : stepCell env st ins rst new ⟨c.width, c.op.mapArgs s.f⟩ =
        ⟨new.vals.push ((stepCell env st ins rst old c).vals.getD old.vals.size 0),
          (stepCell env st ins rst old c).subs⟩ := by
      obtain ⟨w, op⟩ := c
      cases hi : op.isInst
      · rw [stepCell_noninst env st ins rst new w _ (by rw [mapArgs_isInst]; exact hi),
          stepCell_noninst env st ins rst old w op hi,
          evalBV_mapArgs s.f (frame st ins old.vals) (frame st ins new.vals) w op hval rfl rfl rfl, getD_push_eq,
          h.2.2.1]
      · cases op with
        | inst j args outs =>
          have ha : (args.map s.f).toArray.map (new.vals.getD · 0) = args.toArray.map (old.vals.getD · 0) := by
            apply Array.ext (by simp)
            intro i h1 h2
            simp only [Array.getElem_map, List.getElem_toArray, List.getElem_map]
            exact hval _ (by simp [Op.args])
          simp only [Op.mapArgs, stepCell, h.2.2.1, ha, getD_push_eq]
        | _ => simp [Op.isInst] at hi
    rw [hnew]
    refine ⟨by simp [h.1, hsz], by simp [h.2.1], rfl, fun j t hjt => ?_⟩
    simp only [Array.getElem?_push] at hjt
    split at hjt
    · rename_i hj
      simp only [Option.join_some, Option.some.injEq] at hjt
      subst hjt; subst hj
      refine ⟨show s.size < s.size + 1 by omega, ?_⟩
      rw [← h.2.1, getD_push_eq, h.1]
    · obtain ⟨ht, hv⟩ := h.2.2.2 j t hjt
      have hj : j < old.vals.size := by
        rcases Nat.lt_or_ge j s.ren.size with h' | h'
        · rw [← h.1]; exact h'
        · rw [Array.getElem?_eq_none h'] at hjt; cases hjt
      refine ⟨show t < s.size + 1 by omega, ?_⟩
      rw [getD_push_lt _ _ _ (by rw [h.2.1]; exact ht), hv, Build.stepCell_prefix _ _ _ _ _ _ _ hj]
  · rename_i hdrop
    simp only [hdrop] at hok
    refine ⟨hok, ?_⟩
    simp only [Option.toList_none, List.foldl_nil]
    have hinst : c.op.isInst = false := by
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hdrop; exact hdrop.2
    have hsubs : (stepCell env st ins rst old c).subs = old.subs := by
      obtain ⟨w, op⟩ := c
      cases op <;> simp [Op.isInst] at hinst <;> rfl
    refine ⟨by simp [h.1, hsz], h.2.1, by rw [hsubs]; exact h.2.2.1, fun j t hjt => ?_⟩
    simp only [Array.getElem?_push] at hjt
    split at hjt
    · simp at hjt
    · obtain ⟨ht, hv⟩ := h.2.2.2 j t hjt
      have hj : j < old.vals.size := by
        rcases Nat.lt_or_ge j s.ren.size with h' | h'
        · rw [← h.1]; exact h'
        · rw [Array.getElem?_eq_none h'] at hjt; cases hjt
      exact ⟨ht, by rw [hv, Build.stepCell_prefix _ _ _ _ _ _ _ hj]⟩

theorem cp_ok_mono (live : Array Bool) (s : Cp) (c : Cell) : (s.step live c).1.ok = true → s.ok = true := by
  unfold Cp.step; split <;> simp_all

theorem cpList_ok_mono (live : Array Bool) : ∀ (cs : List Cell) (s : Cp), (cpList live s cs).1.ok = true → s.ok = true
  | [], _, h => h
  | c :: cs, s, h => cp_ok_mono live s c (cpList_ok_mono live cs _ h)

theorem cpList_sound (live : Array Bool) : ∀ (cs : List Cell) (s : Cp) (old new : Acc), CpRel s old new →
    (cpList live s cs).1.ok = true →
    CpRel (cpList live s cs).1 (cs.foldl (stepCell env st ins rst) old)
      ((cpList live s cs).2.foldl (stepCell env st ins rst) new)
  | [], _, _, _, h, _ => h
  | c :: cs, s, old, new, h, hok => by
    have hok1 := cpList_ok_mono live cs _ hok
    obtain ⟨-, h1⟩ := cpStep_sound env st ins rst live s old new c h hok1
    simp only [cpList, List.foldl_cons, List.foldl_append]
    exact cpList_sound live cs _ _ _ h1 hok

end

theorem _root_.HDLean.Rtl.Module.compact_evalWith (m : Module) (env : Nat → Sem) :
    m.compact.evalWith env = m.evalWith env := by
  funext st ins rst
  unfold Module.compact
  dsimp only
  split
  · rename_i hc
    simp only [Bool.and_eq_true, refsOk, Array.all_eq_true] at hc
    obtain ⟨hok, ⟨hout, hreg⟩, hmem⟩ := hc
    have hrel := cpList_sound env st ins rst m.liveCells m.cells.toList ⟨#[], 0, true⟩ ⟨#[], #[]⟩ ⟨#[], #[]⟩
      ⟨rfl, rfl, rfl, fun j t h => by simp at h⟩ hok
    generalize hr : cpList m.liveCells ⟨#[], 0, true⟩ m.cells.toList = r at hrel hok hout hreg hmem
    have hnew : (compactWith m r.1 r.2).values env st ins rst = r.2.foldl (stepCell env st ins rst) ⟨#[], #[]⟩ := by
      simp [Module.values, compactWith, ← Array.foldl_toList]
    have hold : m.values env st ins rst = m.cells.toList.foldl (stepCell env st ins rst) ⟨#[], #[]⟩ := by
      simp [Module.values, ← Array.foldl_toList]
    have fv := fun x hx => hrel.f_val x hx
    simp only [Module.evalWith, hnew, hold]
    simp only [compactWith]
    congr 1
    · apply Array.ext (by simp)
      intro i h1 h2
      simp only [Array.getElem_map]
      exact fv _ (hout i (by simpa using h1))
    · congr 1
      · apply Array.ext (by simp)
        intro i h1 h2
        have hi : i < m.regs.size := by simpa using h1
        have hn := fv _ (hreg i hi)
        simp only [Array.getElem_map, Reg.update]
        cases m.regs[i].reset <;> simp [hn]
      · apply Array.ext (by simp)
        intro i h1 h2
        simp only [Array.getElem_mapIdx, Array.getElem_map]
        apply mem_update_rename
        intro p hp
        have hm := hmem i (by simpa using h1)
        try simp only [Array.all_eq_true, Bool.and_eq_true] at hm
        obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hp
        have hm := hm q (by simpa using hq)
        exact ⟨fv _ hm.1.1, fv _ hm.1.2, fv _ hm.2⟩
      · exact hrel.2.2.1
  · rfl

/-- Every module of the compacted design has the original semantics. -/
theorem _root_.HDLean.Rtl.Design.compact_sem (d : Design) : ∀ k, d.compact.sem k = d.sem k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have henv : d.compact.env k = d.env k := by
      funext j
      simp only [Design.env]
      split
      · rename_i hj; exact ih j hj
      · rfl
    cases hm : d.modules[k]? with
    | none =>
      have : d.compact.modules[k]? = none := by simp [Design.compact, hm]
      rw [Design.sem, Design.sem]; simp [this, hm]
    | some m =>
      have : d.compact.modules[k]? = some m.compact := by simp [Design.compact, hm]
      rw [Design.sem_eq _ _ _ this, Design.sem_eq _ _ _ hm, henv, Module.compact_evalWith]

theorem _root_.HDLean.Rtl.Design.compact_step (d : Design) : d.compact.step = d.step := by
  funext st x
  have ht : d.compact.top = d.top := by simp [Design.compact, Design.top]
  simp [Design.step, ht, Design.compact_sem]

theorem _root_.HDLean.Rtl.Design.compact_output (d : Design) : d.compact.output = d.output := by
  funext st ins
  have ht : d.compact.top = d.top := by simp [Design.compact, Design.top]
  simp [Design.output, ht, Design.compact_sem]

/-- Both word-level passes, rewriting then dead-cell removal, kept when the
result passes `Design.check` (it always should; the fallback keeps the CLI total). -/
def _root_.HDLean.Rtl.Design.optimized (d : Design) : Design :=
  if d.optimize.compact.check then d.optimize.compact else d

theorem _root_.HDLean.Rtl.Design.optimized_step (d : Design) : d.optimized.step = d.step := by
  unfold Design.optimized; split
  · rw [Design.compact_step, Design.optimize_step]
  · rfl

theorem _root_.HDLean.Rtl.Design.optimized_output (d : Design) : d.optimized.output = d.output := by
  unfold Design.optimized; split
  · rw [Design.compact_output, Design.optimize_output]
  · rfl

end HDLean.Rtl.Opt
