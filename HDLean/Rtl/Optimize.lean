import HDLean.Rtl.Hoare

/-!
# Word-level rewriting

`Design.optimize` rewrites each cell of each module in place, given what is
known about earlier cells:

* constant folding: an operation on known constants becomes a constant;
* identities: `x & 0`, `x & ~0`, `x | 0`, `x ^ x`, `x + 0`, `x - x`, `x * 1`,
  shifts by zero, muxes with a known select or equal branches, comparisons of a
  cell with itself;
* common subexpressions: a cell equal to an earlier cell (same width, same
  operation on the same operands) becomes a wire to it (`zext` at its width).

Cells are never added, removed or reordered, and registers, memories, outputs
and instances are untouched, so the store layout is unchanged. The hash table
is a hint: a hit is used only if the earlier cell's recorded operation matches.

`Design.optimize_sem`: every module of the optimised design has the semantics
of the original, so `step` and `output` are equal and every theorem about a
design holds for its optimisation (`optimize_step`, `optimize_output`).
-/
namespace HDLean.Rtl.Opt
open HDLean.Rtl.Build

deriving instance Hashable for BinOp, CmpOp, Op

set_option linter.unusedSimpArgs false

/-- Cells an operation reads. -/
def _root_.HDLean.Rtl.Op.args : Op → List Nat
  | .const _ | .input _ | .reg _ => []
  | .memRead _ a | .not a | .neg a | .slice a _ | .zext a | .sext a _ => [a]
  | .bin _ a b | .cmp _ _ a b | .concat a b _ => [a, b]
  | .mux s a b => [s, a, b]
  | .inst _ args _ => args

/-- Depends only on its operand cells (not on inputs, registers, memories or instances). -/
def _root_.HDLean.Rtl.Op.pure : Op → Bool
  | .input _ | .reg _ | .memRead .. | .inst .. => false
  | _ => true

def _root_.HDLean.Rtl.Op.isInst : Op → Bool
  | .inst .. => true
  | _ => false

theorem Op.evalBV_congr (f f' : Frame) (w : Nat) (op : Op) (hv : ∀ x ∈ op.args, f.val x = f'.val x)
    (hi : f.input = f'.input) (hr : f.reg = f'.reg) (hm : f.mem = f'.mem) : op.evalBV f w = op.evalBV f' w := by
  cases op <;> simp only [Op.args, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hv <;>
    simp [Op.evalBV, hi, hr, hm, hv]

theorem Op.evalBV_congr_pure (f f' : Frame) (w : Nat) (op : Op) (hp : op.pure = true)
    (hv : ∀ x ∈ op.args, f.val x = f'.val x) : op.evalBV f w = op.evalBV f' w := by
  cases op <;> simp only [Op.pure, Bool.false_eq_true] at hp <;>
    simp only [Op.args, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hv <;>
    simp [Op.evalBV, hv]

/-! ## Local rewriting -/

/-- `kn x = some v`: cell `x` holds `v`. -/
abbrev Known := Nat → Option Nat

def KnownOk (kn : Known) (f : Frame) : Prop := ∀ x v, kn x = some v → f.val x = v

def kframe (kn : Known) : Frame := ⟨fun x => (kn x).getD 0, fun _ => 0, fun _ => 0, fun _ _ => 0⟩

/-- Cell `x` is known to read as `c` at width `w`. -/
def isK (kn : Known) (w x : Nat) (c : BitVec w) : Bool :=
  match kn x with
  | some v => bv w v == c
  | none => false

theorem isK_spec {kn : Known} {f : Frame} (h : KnownOk kn f) {w x : Nat} {c : BitVec w}
    (hk : isK kn w x c = true) : bv w (f.val x) = c := by
  unfold isK at hk
  split at hk
  · rename_i v hv
    rw [h x v hv]; simpa using hk
  · cases hk

def identBin (kn : Known) (w : Nat) (o : BinOp) (a b : Nat) : Op :=
  match o with
  | .and =>
    if isK kn w a 0 then .const 0
    else if isK kn w b 0 then .const 0
    else if isK kn w b (BitVec.allOnes w) then .zext a
    else if isK kn w a (BitVec.allOnes w) then .zext b
    else if a == b then .zext a
    else .bin o a b
  | .or =>
    if isK kn w a (BitVec.allOnes w) then .const (BitVec.allOnes w).toNat
    else if isK kn w b (BitVec.allOnes w) then .const (BitVec.allOnes w).toNat
    else if isK kn w b 0 then .zext a
    else if isK kn w a 0 then .zext b
    else if a == b then .zext a
    else .bin o a b
  | .xor =>
    if a == b then .const 0
    else if isK kn w b 0 then .zext a
    else if isK kn w a 0 then .zext b
    else .bin o a b
  | .add =>
    if isK kn w b 0 then .zext a
    else if isK kn w a 0 then .zext b
    else .bin o a b
  | .sub =>
    if a == b then .const 0
    else if isK kn w b 0 then .zext a
    else .bin o a b
  | .mul =>
    if isK kn w a 0 then .const 0
    else if isK kn w b 0 then .const 0
    else if isK kn w b 1 then .zext a
    else if isK kn w a 1 then .zext b
    else .bin o a b
  | .shl | .lshr | .ashr => if kn b == some 0 then .zext a else .bin o a b
  | _ => .bin o a b

def identCmp (w : Nat) (o : CmpOp) (cw a b : Nat) : Op :=
  if a == b then
    match o with
    | .eq | .ule | .sle => .const ((BitVec.ofBool true).setWidth w).toNat
    | .ne | .ult | .slt => .const ((BitVec.ofBool false).setWidth w).toNat
  else .cmp o cw a b

def ident (kn : Known) (w : Nat) : Op → Op
  | .bin o a b => identBin kn w o a b
  | .cmp o cw a b => identCmp w o cw a b
  | .mux s a b =>
    if a == b then .zext a
    else match kn s with
      | some v => if v.testBit 0 then .zext a else .zext b
      | none => .mux s a b
  | op => op

/-- Fold constants, else apply an identity. -/
def simp1 (kn : Known) (w : Nat) (op : Op) : Op :=
  if op.pure && op.args.all (fun x => (kn x).isSome) then .const (op.evalBV (kframe kn) w).toNat
  else ident kn w op

theorem identBin_sound {kn : Known} {f : Frame} (h : KnownOk kn f) (w : Nat) (o : BinOp) (a b : Nat) :
    (identBin kn w o a b).evalBV f w = (Op.bin o a b).evalBV f w := by
  have k := fun x c (hx : isK kn w x c = true) => isK_spec h hx
  cases o <;> simp only [identBin]
  all_goals
    repeat' (
      split
      · rename_i h1
        first
        | (simp only [beq_iff_eq] at h1; subst h1; simp [Op.evalBV, BinOp.eval])
        | (simp only [beq_iff_eq] at h1; have h2 := h b 0 h1; simp [Op.evalBV, BinOp.eval, h2])
        | (have h2 := k _ _ h1; simp only [Op.evalBV, bv_toNat]; simp [BinOp.eval, h2]))
  all_goals rfl

theorem identCmp_sound (f : Frame) (w : Nat) (o : CmpOp) (cw a b : Nat) :
    (identCmp w o cw a b).evalBV f w = (Op.cmp o cw a b).evalBV f w := by
  unfold identCmp
  split
  · rename_i hab
    simp only [beq_iff_eq] at hab
    subst hab
    cases o <;> simp only [Op.evalBV, bv_toNat, CmpOp.eval] <;>
      simp [BitVec.ule, BitVec.sle, BitVec.ult, BitVec.slt]
  · rfl

theorem ident_sound {kn : Known} {f : Frame} (h : KnownOk kn f) (w : Nat) (op : Op) :
    (ident kn w op).evalBV f w = op.evalBV f w := by
  cases op with
  | bin o a b => exact identBin_sound h w o a b
  | cmp o cw a b => exact identCmp_sound f w o cw a b
  | mux s a b =>
    simp only [ident]
    split
    · rename_i hab
      simp only [beq_iff_eq] at hab; subst hab
      simp [Op.evalBV]
    · split
      · rename_i v hv
        have := h s v hv
        split <;> simp_all [Op.evalBV]
      · rfl
  | _ => rfl

theorem simp1_sound {kn : Known} {f : Frame} (h : KnownOk kn f) (w : Nat) (op : Op) :
    (simp1 kn w op).evalBV f w = op.evalBV f w := by
  unfold simp1
  split
  · rename_i hc
    simp only [Bool.and_eq_true, List.all_eq_true] at hc
    simp only [Op.evalBV, bv_toNat]
    apply Op.evalBV_congr_pure _ _ _ _ hc.1
    intro x hx
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hc.2 x hx)
    simp [kframe, hv, h x v hv]
  · exact ident_sound h w op

theorem simp1_notInst (kn : Known) (w : Nat) (op : Op) (hop : op.isInst = false) :
    (simp1 kn w op).isInst = false := by
  unfold simp1
  split
  · rfl
  · cases op with
    | inst => simp [Op.isInst] at hop
    | bin o a b =>
      simp only [ident, identBin]
      cases o <;> simp only <;> (repeat' split) <;> rfl
    | cmp o cw a b =>
      simp only [ident, identCmp]
      split
      · cases o <;> rfl
      · rfl
    | mux s a b =>
      simp only [ident]
      (repeat' split) <;> rfl
    | _ => simp [ident, Op.isInst]

/-! ## The module pass -/

structure Info where
  known : Option Nat
  op : Option Op
  width : Nat

structure St where
  info : Array Info
  table : Std.HashMap (Nat × Op) Nat

def St.kn (s : St) : Known := fun x => (s.info[x]?).bind (·.known)

def St.hit (s : St) (w : Nat) (o : Op) (j : Nat) : Bool :=
  match s.info[j]? with
  | some i => i.width == w && i.op == some o
  | none => false

/-- Rewrite one cell; record what is known about it. -/
def St.step (s : St) (c : Cell) : St × Cell :=
  if c.op.isInst then (⟨s.info.push ⟨none, none, c.width⟩, s.table⟩, c)
  else
    let k := s.info.size
    let o1 := simp1 s.kn c.width c.op
    let o2 := match o1 with
      | .const _ => o1
      | _ => match s.table[(c.width, o1)]? with
        | some j => if s.hit c.width o1 j then .zext j else o1
        | none => o1
    let known := match o1 with
      | .const v => some (bv c.width v).toNat
      | _ => none
    let fact := if o1.args.all (· < k) then some o1 else none
    let table := if fact.isSome && !(s.table.contains (c.width, o1)) then s.table.insert (c.width, o1) k else s.table
    (⟨s.info.push ⟨known, fact, c.width⟩, table⟩, ⟨c.width, o2⟩)

def rwList : St → List Cell → List Cell
  | _, [] => []
  | s, c :: cs => (s.step c).2 :: rwList (s.step c).1 cs

def _root_.HDLean.Rtl.Module.optimize (m : Module) : Module :=
  { m with cells := (rwList ⟨#[], {}⟩ m.cells.toList).toArray }

def _root_.HDLean.Rtl.Design.optimize (d : Design) : Design := ⟨d.modules.map Module.optimize⟩

/-! ## Soundness -/

section
variable (env : Nat → Sem) (st : Store) (ins : Array Nat) (rst : Bool)

/-- What the pass records about earlier cells holds of their values. -/
def Inv (s : St) (acc : Acc) : Prop :=
  s.info.size = acc.vals.size ∧ ∀ j (hj : j < s.info.size),
    (∀ v, s.info[j].known = some v → acc.vals.getD j 0 = v) ∧
    (∀ o, s.info[j].op = some o → (∀ x ∈ o.args, x < j) ∧ o.isInst = false ∧
      acc.vals.getD j 0 = (o.evalBV (frame st ins acc.vals) s.info[j].width).toNat)

theorem frame_push_val (vals : Array Nat) (v x : Nat) (hx : x < vals.size) :
    (frame st ins (vals.push v)).val x = (frame st ins vals).val x := by
  simp [frame, Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt hx]

theorem Inv.knownOk {s : St} {acc : Acc} (h : Inv st ins s acc) : KnownOk s.kn (frame st ins acc.vals) := by
  intro x v hx
  simp only [St.kn] at hx
  cases hi : s.info[x]? with
  | none => simp [hi] at hx
  | some i =>
    simp only [hi, Option.bind_some] at hx
    have hlt : x < s.info.size := by
      rcases Nat.lt_or_ge x s.info.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hi; cases hi
    have e : s.info[x] = i := by rw [Array.getElem?_eq_getElem hlt] at hi; exact Option.some.inj hi
    exact (h.2 x hlt).1 v (by rw [e]; exact hx)

/-- Pushing a value keeps every recorded fact. -/
theorem Inv.push {s : St} {acc : Acc} (h : Inv st ins s acc) (i : Info) (v : Nat) (subs : Array Store)
    (hk : ∀ u, i.known = some u → v = u)
    (ho : ∀ o, i.op = some o → (∀ x ∈ o.args, x < s.info.size) ∧ o.isInst = false ∧
      v = (o.evalBV (frame st ins (acc.vals.push v)) i.width).toNat) (table : Std.HashMap (Nat × Op) Nat) :
    Inv st ins ⟨s.info.push i, table⟩ ⟨acc.vals.push v, subs⟩ := by
  refine ⟨by simp [h.1], fun j hj => ?_⟩
  simp only [Array.size_push] at hj
  by_cases hjs : j < s.info.size
  · have old := h.2 j hjs
    have hjv : j < acc.vals.size := by rw [← h.1]; exact hjs
    have gv : (acc.vals.push v).getD j 0 = acc.vals.getD j 0 := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt hjv]
    dsimp only
    simp only [Array.getElem_push, hjs, ↓reduceDIte, gv]
    refine ⟨old.1, fun o hoj => ?_⟩
    obtain ⟨ha, hn, he⟩ := old.2 o hoj
    refine ⟨ha, hn, ?_⟩
    rw [he, Op.evalBV_congr (frame st ins acc.vals) (frame st ins (acc.vals.push v)) _ _
      (fun x hx => (frame_push_val st ins _ _ _ (by have := ha x hx; omega)).symm) rfl rfl rfl]
    have e : (s.info.push i)[j]'(by simp; omega) = s.info[j] := Array.getElem_push_lt hjs
    rw [e]
  · have hj' : j = s.info.size := by omega
    subst hj'
    have gv : (acc.vals.push v).getD s.info.size 0 = v := by simp [Array.getD_eq_getD_getElem?, h.1]
    simp only [Array.getElem_push, Nat.lt_irrefl, ↓reduceDIte, gv]
    have e : (s.info.push i)[s.info.size]'(by simp) = i := Array.getElem_push_eq
    refine ⟨hk, fun o hoj => ?_⟩
    obtain ⟨a, b, c⟩ := ho o hoj
    rw [e]
    exact ⟨a, b, c⟩

theorem step_sound (s : St) (acc : Acc) (c : Cell) (h : Inv st ins s acc) :
    stepCell env st ins rst acc (s.step c).2 = stepCell env st ins rst acc c ∧
    Inv st ins (s.step c).1 (stepCell env st ins rst acc c) := by
  unfold St.step
  split
  · rename_i hinst
    refine ⟨rfl, ?_⟩
    cases c with | mk w op =>
    cases op <;> simp only [Op.isInst, Bool.false_eq_true] at hinst
    rename_i j args outs
    simp only [stepCell]
    exact Inv.push st ins h _ _ _ (fun u hu => by cases hu) (fun o ho => by cases ho) _
  · rename_i hinst
    simp only [Bool.not_eq_true] at hinst
    have hko := Inv.knownOk st ins h
    have s1 := simp1_sound hko c.width c.op
    have ni1 := simp1_notInst s.kn c.width c.op hinst
    generalize ho1 : simp1 s.kn c.width c.op = o1 at s1 ni1
    -- the value pushed by the original cell
    have hc : stepCell env st ins rst acc c = ⟨acc.vals.push (c.op.evalBV (frame st ins acc.vals) c.width).toNat, acc.subs⟩ := by
      cases c with | mk w op =>
      cases op <;> simp only [Op.isInst, Bool.true_eq_false] at hinst <;> rfl
    -- the rewritten operation computes the same value
    have ho2 : ∀ o2 : Op, o2.isInst = false → o2.evalBV (frame st ins acc.vals) c.width = c.op.evalBV (frame st ins acc.vals) c.width →
        stepCell env st ins rst acc ⟨c.width, o2⟩ = stepCell env st ins rst acc c := by
      intro o2 hn he
      rw [hc]
      cases o2 <;> simp only [Op.isInst, Bool.true_eq_false] at hn <;> simp only [stepCell] <;>
        exact congrArg (fun x : BitVec c.width => ({ vals := acc.vals.push x.toNat, subs := acc.subs } : Acc)) he
    refine ⟨?_, ?_⟩
    · apply ho2
      · split
        · rfl
        · split
          · split <;> first | rfl | exact ni1
          · exact ni1
      · split
        · rename_i v hv; rw [← s1]
        · split
          · rename_i j hj
            split
            · rename_i hhit
              unfold St.hit at hhit
              split at hhit
              · rename_i i hi
                simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at hhit
                obtain ⟨hw, hop⟩ := hhit
                have hlt : j < s.info.size := by
                  rcases Nat.lt_or_ge j s.info.size with h' | h'
                  · exact h'
                  · rw [Array.getElem?_eq_none h'] at hi; cases hi
                have e : s.info[j] = i := by rw [Array.getElem?_eq_getElem hlt] at hi; exact Option.some.inj hi
                obtain ⟨-, -, hv⟩ := (h.2 j hlt).2 o1 (by rw [e, hop])
                rw [show Op.evalBV (frame st ins acc.vals) c.width (Op.zext j) = bv c.width ((frame st ins acc.vals).val j) from rfl, ← s1]
                change bv c.width (acc.vals.getD j 0) = _
                rw [hv, e, hw, bv_toNat]
              · cases hhit
            · exact s1
          · exact s1
    · rw [hc]
      apply Inv.push st ins h
      · intro u hu
        split at hu
        · rename_i v
          cases hu
          rw [← s1]; rfl
        · cases hu
      · intro o hoo
        have hargs : (o1.args.all fun x => decide (x < s.info.size)) = true := by
          cases hb : (o1.args.all fun x => decide (x < s.info.size))
          · simp [hb] at hoo
          · rfl
        have ho : o = o1 := by simp [hargs] at hoo; exact hoo.symm
        subst ho
        simp only [List.all_eq_true, decide_eq_true_eq] at hargs
        refine ⟨hargs, ni1, ?_⟩
        have hx := Op.evalBV_congr (frame st ins acc.vals)
          (frame st ins (acc.vals.push (Op.evalBV (frame st ins acc.vals) c.width c.op).toNat)) c.width o
          (fun x hx => (frame_push_val st ins _ _ _ (by have := hargs x hx; rw [← h.1]; exact this)).symm) rfl rfl rfl
        rw [← hx, s1]

theorem rwList_sound : ∀ (cs : List Cell) (s : St) (acc : Acc), Inv st ins s acc →
    (rwList s cs).foldl (stepCell env st ins rst) acc = cs.foldl (stepCell env st ins rst) acc
  | [], _, _, _ => rfl
  | c :: cs, s, acc, h => by
    obtain ⟨e, h'⟩ := step_sound env st ins rst s acc c h
    simp only [rwList, List.foldl_cons, e]
    exact rwList_sound cs _ _ h'

end

theorem _root_.HDLean.Rtl.Module.optimize_values (m : Module) (env : Nat → Sem) (st : Store) (ins : Array Nat)
    (rst : Bool) : m.optimize.values env st ins rst = m.values env st ins rst := by
  simp only [Module.values, Module.optimize, ← Array.foldl_toList, List.toList_toArray]
  exact rwList_sound env st ins rst _ _ _ ⟨rfl, fun j hj => by simp at hj⟩

theorem _root_.HDLean.Rtl.Module.optimize_evalWith (m : Module) (env : Nat → Sem) :
    m.optimize.evalWith env = m.evalWith env := by
  funext st ins rst
  simp only [Module.evalWith, Module.optimize_values]
  rfl

/-- Every module of the optimised design has the original semantics. -/
theorem _root_.HDLean.Rtl.Design.optimize_sem (d : Design) : ∀ k, d.optimize.sem k = d.sem k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have henv : d.optimize.env k = d.env k := by
      funext j
      simp only [Design.env]
      split
      · rename_i hj; exact ih j hj
      · rfl
    cases hm : d.modules[k]? with
    | none =>
      have : d.optimize.modules[k]? = none := by simp [Design.optimize, hm]
      rw [Design.sem, Design.sem]; simp [this, hm]
    | some m =>
      have : d.optimize.modules[k]? = some m.optimize := by simp [Design.optimize, hm]
      rw [Design.sem_eq _ _ _ this, Design.sem_eq _ _ _ hm, henv, Module.optimize_evalWith]

theorem _root_.HDLean.Rtl.Design.optimize_top (d : Design) : d.optimize.top = d.top := by
  simp [Design.optimize, Design.top]

theorem _root_.HDLean.Rtl.Design.optimize_step (d : Design) : d.optimize.step = d.step := by
  funext st x
  simp [Design.step, Design.optimize_top, Design.optimize_sem]

theorem _root_.HDLean.Rtl.Design.optimize_output (d : Design) : d.optimize.output = d.output := by
  funext st ins
  simp [Design.output, Design.optimize_top, Design.optimize_sem]

end HDLean.Rtl.Opt
