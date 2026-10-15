import HDLean.Backend.Validate
import Std.Data.TreeMap

set_option linter.unusedSimpArgs false
namespace HDLean.Backend.Local

def run (gs : List Gate) (v : Array Bool) : Array Bool :=
  gs.foldl (fun v g => v.push (litValue v g.a && litValue v g.b)) v

def Ordered : Nat → List Gate → Prop
  | _, [] => True
  | n, g::gs => g.lhs = n ∧ g.a/2 < n ∧ g.b/2 < n ∧ Ordered (n+1) gs

def orderedDecidable (n : Nat) : (gs : List Gate) → Decidable (Ordered n gs)
  | [] => isTrue trivial
  | g::gs =>
    letI := orderedDecidable (n+1) gs
    inferInstanceAs (Decidable (g.lhs = n ∧ g.a/2 < n ∧ g.b/2 < n ∧ Ordered (n+1) gs))

instance (n gs) : Decidable (Ordered n gs) := orderedDecidable n gs

def Extends (a b : Array Bool) : Prop :=
  a.size ≤ b.size ∧ ∀ j, j < a.size → b[j]?.getD false = a[j]?.getD false

theorem extends_refl (a : Array Bool) : Extends a a := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem extends_push (a : Array Bool) (b : Bool) : Extends a (a.push b) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  simp [Array.getElem?_push, Nat.ne_of_lt hj]

theorem extends_trans {a b c : Array Bool} (h : Extends a b) (k : Extends b c) : Extends a c :=
  ⟨Nat.le_trans h.1 k.1, fun j hj => (k.2 j (Nat.lt_of_lt_of_le hj h.1)).trans (h.2 j hj)⟩

theorem lit_extends {a b : Array Bool} (h : Extends a b) {l : Lit} (hl : l/2 < a.size) :
    litValue b l = litValue a l := by simp only [litValue, h.2 _ hl]

theorem run_extends (gs : List Gate) (a : Array Bool) : Extends a (run gs a) := by
  induction gs generalizing a with
  | nil => exact extends_refl _
  | cons g gs ih => exact extends_trans (extends_push _ _) (ih _)

theorem run_size (gs : List Gate) (a : Array Bool) : (run gs a).size = a.size + gs.length := by
  induction gs generalizing a with
  | nil => simp [run]
  | cons g gs ih => simp only [run, List.foldl_cons] at *; rw [ih]; simp; omega

theorem lit_even (v : Array Bool) (n : Nat) : litValue v (2*n) = v[n]?.getD false := by
  simp [litValue, Nat.mul_div_cancel_left]

theorem lit_invert (v : Array Bool) (l : Lit) : litValue v (invert l) = !(litValue v l) := by
  simp only [litValue, invert, Nat.xor_div_two, Nat.reduceDiv, Nat.xor_zero]
  have h : ((l ^^^ 1) % 2 == 1) = !(l % 2 == 1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true', beq_iff_eq, Nat.xor_mod_two_eq_one]
    simp
  rw [h]
  cases v[l/2]?.getD false <;> cases l%2 == 1 <;> rfl

/-- Every accepted local gate equation holds in the final graph environment;
the proof uses bounded operands and preservation of earlier array cells. -/
theorem run_gate (gs : List Gate) (a : Array Bool) (h : Ordered a.size gs)
    (g : Gate) (hg : g ∈ gs) :
    litValue (run gs a) (2*g.lhs) =
      (litValue (run gs a) g.a && litValue (run gs a) g.b) := by
  induction gs generalizing a with
  | nil => simp at hg
  | cons first rest ih =>
    rcases h with ⟨hl, ha, hb, ht⟩
    rcases List.mem_cons.mp hg with heq | hg
    · subst g
      let pushed := a.push (litValue a first.a && litValue a first.b)
      have he := run_extends rest pushed
      have he' := run_extends (first::rest) a
      rw [lit_extends he' ha, lit_extends he' hb, lit_even, hl]
      change (run rest pushed)[a.size]?.getD false = _
      rw [he.2 _ (by simp [pushed])]
      simp [pushed]
    · exact ih _ (by simpa using ht) hg

abbrev Meaning (i r : Nat) := Vector Bool i → Vector Bool r → Bool → Bool

def meaning (g : Graph) (l : Lit) : Meaning i r := fun xs s rst =>
  litValue (g.values (xs.toArray.push rst) s.toArray) l

def source (e : Expr d i r) : Meaning i r := fun xs s _ => e.eval (fun j => xs[j]) (fun j => s[j])

structure Context (g : Graph) (i r : Nat) : Prop where
  inputs : g.inputs = i+1
  latches : g.latches = r
  ordered : Ordered (g.inputs+g.latches+1) g.gates.toList

theorem context_ordered (h : Context g i r) (xs : Vector Bool i) (s : Vector Bool r) (rst) :
    Ordered (#[false] ++ xs.toArray.push rst ++ s.toArray).size g.gates.toList := by
  simpa [h.inputs, h.latches, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h.ordered

theorem initial_read (g : Graph) (xs : Vector Bool i) (s : Vector Bool r) (rst) (j : Nat)
    (hj : j < (#[false] ++ xs.toArray.push rst ++ s.toArray).size) :
    (g.values (xs.toArray.push rst) s.toArray)[j]?.getD false =
      (#[false] ++ xs.toArray.push rst ++ s.toArray)[j]?.getD false := by
  simpa [run, Graph.values, Array.foldl_toList] using (run_extends g.gates.toList _).2 j hj

theorem meaning_zero (g : Graph) : meaning (i := i) (r := r) g 0 = fun _ _ _ => false := by
  funext xs s rst
  simp only [meaning, litValue, Nat.zero_div, Nat.zero_mod, Nat.reduceBEq, Bool.xor_false]
  rw [initial_read g xs s rst 0 (by simp; omega)]
  simp [Array.getElem?_append]

theorem meaning_one (g : Graph) : meaning (i := i) (r := r) g 1 = fun _ _ _ => true := by
  funext xs s rst
  have hz := congrFun (congrFun (congrFun (meaning_zero (i := i) (r := r) g) xs) s) rst
  simpa [meaning, litValue] using congrArg Bool.not hz

theorem meaning_invert (g : Graph) (l : Lit) : meaning (i := i) (r := r) g (invert l) =
    fun xs s rst => !(meaning g l xs s rst) := by funext xs s rst; exact lit_invert _ _

theorem meaning_input (g : Graph) (j : Fin i) : meaning (r := r) g (2*(j.val+1)) =
    fun (xs : Vector Bool i) _ _ => xs[j] := by
  funext xs s rst
  rw [meaning, lit_even, initial_read g xs s rst _ (by simp; omega)]
  simp [Array.getElem?_append, Array.getElem?_push, j.isLt, Nat.ne_of_lt j.isLt, show j.val < i+1 by omega, Array.getElem_push]

theorem meaning_reset (g : Graph) : meaning (i := i) (r := r) g (2*(i+1)) =
    fun _ _ rst => rst := by
  funext xs s rst
  rw [meaning, lit_even, initial_read g xs s rst _ (by simp; omega)]
  simp [Array.getElem?_append, Array.getElem?_push, Array.getElem_push]

theorem meaning_reg (g : Graph) (j : Fin r) : meaning (i := i) g (2*(i+2+j.val)) =
    fun _ (s : Vector Bool r) _ => s[j] := by
  funext xs s rst
  rw [meaning, lit_even, initial_read g xs s rst _ (by simp; omega)]
  simp [Array.getElem?_append, show ¬i+2+j.val < 1+(i+1) by omega]

theorem meaning_gate (ctx : Context g i r) (gate : Gate) (hg : gate ∈ g.gates.toList) :
    meaning g (2*gate.lhs) = fun xs s rst => meaning (i := i) (r := r) g gate.a xs s rst && meaning g gate.b xs s rst := by
  funext xs s rst
  simpa [run, Graph.values, meaning, Array.foldl_toList] using run_gate g.gates.toList _ (context_ordered ctx xs s rst) gate hg

structure Checked (g : Graph) (f : Meaning i r) where
  lit : Lit
  correct : meaning g lit = f

structure AndEntry (g : Graph) (i r : Nat) where
  a : Lit
  b : Lit
  out : Checked g (fun xs s rst => meaning (i := i) (r := r) g a xs s rst && meaning g b xs s rst)

abbrev Index (g : Graph) (i r : Nat) := Std.TreeMap (Lit × Lit) (AndEntry g i r) (fun a b => (compare a.1 b.1).then (compare a.2 b.2))

def index (ctx : Context g i r) : Index g i r := Id.run do
  let mut table := {}
  for gate in g.gates.toList.attach do
    let e : AndEntry g i r := ⟨gate.val.a, gate.val.b, ⟨2*gate.val.lhs, meaning_gate ctx _ gate.property⟩⟩
    table := table.insert (gate.val.a,gate.val.b) e
  return table

variable {f h p : Meaning i r}

def neg (a : Checked g f) : Checked g (fun xs s rst => !(f xs s rst)) :=
  ⟨invert a.lit, by rw [meaning_invert, a.correct]⟩

def constant (g : Graph) (b : Bool) : Checked g (fun (_ : Vector Bool i) (_ : Vector Bool r) _ => b) :=
  if h : b then ⟨1, by simpa [h] using meaning_one g⟩ else ⟨0, by simpa [h] using meaning_zero g⟩

/-- Search-tree entries are proof carrying; both keys are checked on every hit.
An arbitrary or corrupted index can only cause rejection or slower search. -/
def conjunction (table : Index g i r) (a : Checked g f) (b : Checked g h) :
    Option (Checked g (fun xs s rst => f xs s rst && h xs s rst)) := by
  exact Id.run do
    if ha : a.lit = 0 then
      return some ⟨0, by simp only [← a.correct, ha, meaning_zero, Bool.false_and]⟩
    if hb : b.lit = 0 then
      return some ⟨0, by simp only [← b.correct, hb, meaning_zero, Bool.and_false]⟩
    if ha : a.lit = 1 then
      return some ⟨b.lit, by rw [← a.correct, ha, meaning_one]; simpa using b.correct⟩
    if hb : b.lit = 1 then
      return some ⟨a.lit, by rw [← b.correct, hb, meaning_one]; simpa using a.correct⟩
    if hab : a.lit = b.lit then
      return some ⟨a.lit, by simp only [← a.correct, ← b.correct, hab, Bool.and_self]⟩
    if hab : a.lit = invert b.lit then
      return some ⟨0, by rw [← a.correct, ← b.correct, hab, meaning_invert]; simp; exact meaning_zero g⟩
    let key := (max a.lit b.lit, min a.lit b.lit)
    let some e := table[key]? | return none
    if he : e.a = a.lit ∧ e.b = b.lit then
      return some ⟨e.out.lit, by rw [e.out.correct, he.1, he.2, a.correct, b.correct]⟩
    if he : e.a = b.lit ∧ e.b = a.lit then
      return some ⟨e.out.lit, by rw [e.out.correct, he.1, he.2, a.correct, b.correct]; funext xs s rst; exact Bool.and_comm _ _⟩
    return none

def exclusive (table : Index g i r) (a : Checked g f) (b : Checked g h) :
    Option (Checked g (fun xs s rst => Bool.xor (f xs s rst) (h xs s rst))) := do
  let x ← conjunction table a b
  let y ← conjunction table (neg a) (neg b)
  let z ← conjunction table (neg x) (neg y)
  return ⟨z.lit, by rw [z.correct]; funext xs s rst; cases f xs s rst <;> cases h xs s rst <;> rfl⟩

def mux (table : Index g i r) (c : Checked g p) (a : Checked g f) (b : Checked g h) :
    Option (Checked g (fun xs s rst => if p xs s rst then f xs s rst else h xs s rst)) := do
  let x ← conjunction table c a
  let y ← conjunction table (neg c) b
  let z ← conjunction table (neg x) (neg y)
  let z := neg z
  return ⟨z.lit, by rw [z.correct]; funext xs s rst; cases p xs s rst <;> cases f xs s rst <;> cases h xs s rst <;> rfl⟩

deriving instance DecidableEq for Expr

structure Entry (g : Graph) (d i r : Nat) where
  expr : Expr d i r
  value : Checked g (source expr)

abbrev Memo (g : Graph) (d i r : Nat) := Std.TreeMap Nat (Entry g d i r)

private unsafe def pointerHintImpl (e : Expr d i r) : Nat := (ptrAddrUnsafe e).toNat

/-- A transparent cache hint for kernel replay; collisions merely replace an
entry, because expression equality is still checked before every reuse. -/
def fingerprint : Expr d i r → Nat
  | .lit b => if b then 1 else 0
  | .input j => (11*j.val+2)%1000000007
  | .reg j => (13*j.val+3)%1000000007
  | .inv a => (17*fingerprint a+4)%1000000007
  | .and a b => (19*fingerprint a+23*fingerprint b+5)%1000000007
  | .xor a b => (29*fingerprint a+31*fingerprint b+6)%1000000007
  | .mux c a b => (37*fingerprint c+41*fingerprint a+43*fingerprint b+7)%1000000007

/-- This untrusted hint affects only cache placement. Every cache hit checks
structural equality and carries a proof; no correctness property of hints is used. -/
@[implemented_by pointerHintImpl]
def pointerHint (e : Expr d i r) : Nat := fingerprint e

def reuse (entry : Entry g d i r) (e : Expr d i r) : Option (Checked g (source e)) :=
  letI : Decidable (entry.expr = e) := withPtrEqDecEq entry.expr e (fun _ => inferInstance)
  if he : entry.expr = e then some ⟨entry.value.lit, by simpa [he] using entry.value.correct⟩ else none

def checkExpr (table : Index g i r) (hint : Expr d i r → Nat)
    (e : Expr d i r) : StateT (Memo g d i r) Option (Checked g (source e)) := do
  let key := hint e
  if let some value := ((← get)[key]?).bind (fun entry => reuse entry e) then return value
  let result : Checked g (source e) ← match (dependent := true) e with
    | .lit b => pure (constant g b)
    | .input j => pure ⟨2*(j.val+1), meaning_input g j⟩
    | .reg j => pure ⟨2*(i+2+j.val), meaning_reg g j⟩
    | .inv a => return neg (← checkExpr table hint a)
    | .and a b => do liftM (conjunction table (← checkExpr table hint a) (← checkExpr table hint b))
    | .xor a b => do liftM (exclusive table (← checkExpr table hint a) (← checkExpr table hint b))
    | .mux c a b => do liftM (mux table (← checkExpr table hint c) (← checkExpr table hint a) (← checkExpr table hint b))
  modify fun cache => cache.insert key ⟨e,result⟩
  return result

def allChecked [Monad m] {P : α → Prop} (check : (a : α) → m (PLift (P a))) :
    (xs : List α) → m (PLift (∀ a, a ∈ xs → P a))
  | [] => pure ⟨by simp⟩
  | a::as => do
    let ha ← check a
    let hs ← allChecked check as
    return ⟨by intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha.down; exact hs.down _ hx⟩

def checkRoot (value : Checked g f) (l : Lit) : Option (PLift (meaning g l = f)) :=
  if h : l = value.lit then some ⟨by simpa [h] using value.correct⟩ else none

def nextMeaning (c : Circuit d i r o) (j : Fin r) : Meaning i r :=
  fun xs s rst => c.next (fun k => s[k]) ((fun k => xs[k]),rst) j

def outputMeaning (c : Circuit d i r o) (j : Fin o) : Meaning i r :=
  fun xs s _ => c.evalOutput (fun k => s[k]) (fun k => xs[k]) j

def checkNext (c : Circuit d i r o) (table : Index g i r) (hint : Expr d i r → Nat)
    (j : Fin r) : StateT (Memo g d i r) Option (Checked g (nextMeaning c j)) := do
  let v ← checkExpr table hint c.state[j].next
  match h : c.state[j.val].reset with
  | .unreset => return ⟨v.lit, by apply Eq.trans v.correct; funext xs s rst; simp [nextMeaning, Circuit.next, h, source]⟩
  | .hold =>
    let z ← mux table ⟨2*(i+1), meaning_reset g⟩ ⟨2*(i+2+j.val), meaning_reg g j⟩ v
    return ⟨z.lit, by apply Eq.trans z.correct; funext xs s rst; simp [nextMeaning, Circuit.next, h, source]⟩
  | .synchronous b =>
    let z ← mux table ⟨2*(i+1), meaning_reset g⟩ (constant g b) v
    return ⟨z.lit, by apply Eq.trans z.correct; funext xs s rst; simp [nextMeaning, Circuit.next, h, source]⟩

def checkOutput (c : Circuit d i r o) (table : Index g i r) (hint : Expr d i r → Nat)
    (j : Fin o) : StateT (Memo g d i r) Option (Checked g (outputMeaning c j)) := do
  let v ← checkExpr table hint c.output[j]
  return ⟨v.lit, v.correct⟩

def check (g : Graph) (c : Circuit d i r o) (hint : Expr d i r → Nat := pointerHint) :
    Option (PLift (g.Equivalent c)) := do
  if hw : g.wellFormed = true then do
    if hi : g.inputs = i+1 then do
      if hr : g.latches = r then do
        if hn : g.next.size = r then do
          if ho : g.outputs.size = o then do
            if ht : Ordered (g.inputs+g.latches+1) g.gates.toList then do
              let table := index ⟨hi,hr,ht⟩
              let job : StateT (Memo g d i r) Option
                  (PLift (∀ j : Fin r, j ∈ List.finRange r → meaning g g.next[j.val] = nextMeaning c j) ×
                   PLift (∀ j : Fin o, j ∈ List.finRange o → meaning g g.outputs[j.val] = outputMeaning c j)) := do
                let ns ← allChecked (P := fun j : Fin r => meaning g g.next[j.val] = nextMeaning c j) (fun j : Fin r => do liftM (checkRoot (← checkNext c table hint j) g.next[j.val])) (List.finRange r)
                let os ← allChecked (P := fun j : Fin o => meaning g g.outputs[j.val] = outputMeaning c j) (fun j : Fin o => do liftM (checkRoot (← checkOutput c table hint j) g.outputs[j.val])) (List.finRange o)
                return (ns,os)
              let (ns,os) ← job.run' {}
              return ⟨by
                refine ⟨hw,hi,hr,ho,?_⟩
                intro xs s rst
                apply Prod.ext
                · apply Array.ext
                  · simp [Graph.eval, hn]
                  · intro j h₁ h₂
                    have hj : j < r := by simpa using h₂
                    have h := ns.down ⟨j,hj⟩ (List.mem_finRange _)
                    have h := congrFun (congrFun (congrFun h xs) s) rst
                    simpa [Graph.eval, meaning, nextMeaning] using h
                · apply Array.ext
                  · simp [Graph.eval, ho]
                  · intro j h₁ h₂
                    have hj : j < o := by simpa using h₂
                    have h := os.down ⟨j,hj⟩ (List.mem_finRange _)
                    have h := congrFun (congrFun (congrFun h xs) s) rst
                    simpa [Graph.eval, meaning, outputMeaning] using h⟩
            else none
          else none
        else none
      else none
    else none
  else none

end HDLean.Backend.Local

namespace HDLean.Backend

/-- Scalable translation validation: local AIG equations and proof-carrying source
memoization, with no expansion of shared Boolean cones. -/
def Graph.validateLocal (g : Graph) (c : Circuit d i r o)
    (hint : Expr d i r → Nat := Local.pointerHint) : Bool :=
  (Local.check g c hint).isSome

theorem Graph.validateLocal_sound (g : Graph) (c : Circuit d i r o)
    (hint : Expr d i r → Nat := Local.pointerHint)
    (h : g.validateLocal c hint = true) : g.Equivalent c := by
  unfold Graph.validateLocal at h
  cases hc : Local.check g c hint with
  | none => simp [hc] at h
  | some proof => exact proof.down

def checkedCompileLocal (c : Circuit d i r o) : Except String {g : Graph // g.Equivalent c} :=
  let g := compileCandidate c
  match Local.check g c with
  | some proof => .ok ⟨g, proof.down⟩
  | none => .error "local shared-graph translation validation failed"

end HDLean.Backend
