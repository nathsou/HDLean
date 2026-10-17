import HDLean.Netlist.DagTight

/-!
# Proved and-inverter graph optimisation

`Graph.optimize` makes one forward pass over the gates, repeated while the gate
count drops. Each pass:

* drops gates that feed no next-state or output literal;
* folds constants and trivial ANDs (`x ∧ 0`, `x ∧ 1`, `x ∧ x`, `x ∧ ¬x`);
* merges gates with the same two inputs (structural hashing).

Liveness and the hash table are hints, never trusted: each translated
variable's new literal is justified by the rewrite step alone, and a hash hit is
re-checked against the gate it names. If a next-state or output literal cannot
be translated, or the result is not well formed, the pass returns its input.

`Graph.optimize_eval`: the optimised graph has the same next state and outputs
as the original for every input and state (of the declared sizes).
`Graph.optimize_wellFormed`: it is well formed whenever the original is.
-/
namespace HDLean.Backend
open HDLean.Dag

set_option linter.unusedSimpArgs false

/-- The complement of a literal. -/
def negLit (l : Nat) : Nat := if l % 2 = 0 then l + 1 else l - 1

/-- Variables that feed a next-state or output literal, by one backwards sweep
(gates are topologically ordered). A hint only. -/
def Graph.live (g : Graph) : Array Bool := Id.run do
  let n0 := g.inputs + g.latches + 1
  let mut a := Array.replicate (n0 + g.gates.size) false
  for l in g.next do a := a.set! (l / 2) true
  for l in g.outputs do a := a.set! (l / 2) true
  for j in (List.range g.gates.size).reverse do
    if a[n0 + j]! then
      match g.gates[j]? with
      | some gt => a := (a.set! (gt.a / 2) true).set! (gt.b / 2) true
      | none => pure ()
  return a

/-- Rewrite state: the new literal of each old variable translated so far, the
new gates, and a hash table from input pairs to gate indices. -/
structure Rw where
  map : Array (Option Nat)
  gates : Array Gate
  table : Std.HashMap (Nat × Nat) Nat

/-- The new literal of an old literal, if its variable was translated. -/
def Rw.lit (st : Rw) (l : Nat) : Option Nat :=
  match st.map[l / 2]? with
  | some (some m) => some (if l % 2 = 1 then negLit m else m)
  | _ => none

def Rw.emit (n0 : Nat) (st : Rw) (x y : Nat) : Nat × Rw :=
  (2 * (n0 + st.gates.size),
    { st with gates := st.gates.push ⟨n0 + st.gates.size, x, y⟩, table := st.table.insert (x, y) st.gates.size })

/-- A hash hit is used only if the gate it names really is `x ∧ y`. -/
def Rw.hit (n0 : Nat) (st : Rw) (x y k : Nat) : Bool :=
  if h : k < st.gates.size then
    st.gates[k].a == x && st.gates[k].b == y && decide (x / 2 < n0 + k) && decide (y / 2 < n0 + k)
  else false

/-- A literal for `a ∧ b` over the new gates. -/
def Rw.and (n0 : Nat) (st : Rw) (a b : Nat) : Nat × Rw :=
  if a = 0 ∨ b = 0 then (0, st)
  else if a = 1 then (b, st)
  else if b = 1 then (a, st)
  else if a = b then (a, st)
  else if a = negLit b then (0, st)
  else
    let x := min a b
    let y := max a b
    match st.table[(x, y)]? with
    | some k => if st.hit n0 x y k then (2 * (n0 + k), st) else st.emit n0 x y
    | none => st.emit n0 x y

/-- Translate the next old gate (old variable `st.map.size`). -/
def Rw.step (n0 : Nat) (live : Array Bool) (st : Rw) (gt : Gate) : Rw :=
  if live.getD st.map.size false then
    match st.lit gt.a, st.lit gt.b with
    | some a, some b =>
      let p := st.and n0 a b
      { p.2 with map := st.map.push (some p.1) }
    | _, _ => { st with map := st.map.push none }
  else { st with map := st.map.push none }

def Rw.start (n0 : Nat) : Rw := ⟨(Array.range n0).map (fun x => some (2 * x)), #[], {}⟩

/-- One optimisation pass, or the input if it cannot be justified. -/
def Graph.rewrite (g : Graph) : Graph :=
  let n0 := g.inputs + g.latches + 1
  let st := g.gates.toList.foldl (Rw.step n0 g.live) (Rw.start n0)
  if g.next.all (fun l => (st.lit l).isSome) && g.outputs.all (fun l => (st.lit l).isSome) then
    let g' := { g with
      gates := st.gates
      next := g.next.map (fun l => (st.lit l).getD 0)
      outputs := g.outputs.map (fun l => (st.lit l).getD 0) }
    if g'.wellFormed then g' else g
  else g

/-- Passes until the gate count stops dropping (at most `n`). -/
def Graph.optimizeN : Nat → Graph → Graph
  | 0, g => g
  | n + 1, g =>
    let g' := g.rewrite
    if g'.gates.size < g.gates.size then Graph.optimizeN n g' else g'

def Graph.optimize (g : Graph) : Graph := Graph.optimizeN 8 g

/-! ## Literal lemmas -/

theorem litValue_eq_read (v : Array Bool) (l : Nat) : litValue v l = xor (Dag.read v (l / 2)) (l % 2 == 1) := rfl

theorem litValue_extends {a b : Array Bool} (h : Extends a b) (l : Nat) (hl : l / 2 < a.size) :
    litValue b l = litValue a l := by
  simp only [litValue_eq_read, h.2 _ hl]

theorem negLit_div (m : Nat) : negLit m / 2 = m / 2 := by
  unfold negLit
  by_cases h : m % 2 = 0
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]; omega

theorem litValue_negLit (v : Array Bool) (m : Nat) : litValue v (negLit m) = !litValue v m := by
  unfold negLit
  by_cases h : m % 2 = 0
  · simp only [h, ↓reduceIte]
    have h1 : (m + 1) / 2 = m / 2 := by omega
    have h2 : (m + 1) % 2 = 1 := by omega
    simp [litValue_eq_read, h1, h2, h]
  · simp only [h, ↓reduceIte]
    have h1 : (m - 1) / 2 = m / 2 := by omega
    have h2 : (m - 1) % 2 = 0 := by omega
    have h3 : m % 2 = 1 := by omega
    simp [litValue_eq_read, h1, h2, h3]

theorem litValue_double (v : Array Bool) (x : Nat) : litValue v (2 * x) = Dag.read v x := by
  have h1 : 2 * x / 2 = x := by omega
  have h2 : 2 * x % 2 = 0 := by omega
  simp [litValue_eq_read, h1, h2]

theorem read_run_gate (gs : List Gate) (B : Array Bool) (k : Nat) (hk : k < gs.length) :
    Dag.read (run gs B) (B.size + k) =
      (litValue (run (gs.take k) B) gs[k].a && litValue (run (gs.take k) B) gs[k].b) := by
  have e : run gs B = run (gs.drop (k + 1)) ((run (gs.take k) B).push
      (litValue (run (gs.take k) B) gs[k].a && litValue (run (gs.take k) B) gs[k].b)) := by
    conv => lhs; rw [← List.take_append_drop k gs, List.drop_eq_getElem_cons hk]
    rw [run_append]; rfl
  have hs : (run (gs.take k) B).size = B.size + k := by simp; omega
  rw [e, (run_extends _ _).2 _ (by simp; omega)]
  have h2 : B.size + k = (run (gs.take k) B).size := hs.symm
  rw [h2]; unfold Dag.read; rw [Array.getElem?_push_size]; rfl

theorem run_take_extends (gs : List Gate) (B : Array Bool) (k : Nat) :
    Extends (run (gs.take k) B) (run gs B) := by
  conv => rhs; rw [← List.take_append_drop k gs]
  rw [run_append]; exact run_extends _ _

/-! ## The rewrite step -/

section
variable {B : Array Bool}

/-- Every translated variable's new literal computes the old variable's value. -/
def Rw.Ok (B V : Array Bool) (st : Rw) : Prop :=
  st.map.size = V.size ∧ ∀ x l, st.map[x]? = some (some l) →
    l / 2 < (run st.gates.toList B).size ∧ litValue (run st.gates.toList B) l = Dag.read V x

theorem Rw.lit_ok {st : Rw} {V : Array Bool} {l m : Nat} (h : st.Ok B V) (hl : st.lit l = some m) :
    m / 2 < (run st.gates.toList B).size ∧ litValue (run st.gates.toList B) m = litValue V l := by
  unfold Rw.lit at hl
  split at hl
  · rename_i m0 hm
    obtain ⟨hb, hv⟩ := h.2 _ _ hm
    cases hl
    by_cases h1 : l % 2 = 1
    · simp only [h1, ↓reduceIte]
      refine ⟨by rw [negLit_div]; exact hb, ?_⟩
      rw [litValue_negLit, hv, litValue_eq_read]; simp [h1]
    · simp only [h1, ↓reduceIte]
      refine ⟨hb, ?_⟩
      have h2 : l % 2 = 0 := by omega
      rw [hv, litValue_eq_read]; simp [h2]
  · cases hl

theorem lit0 (hpos : 0 < B.size) (hB0 : Dag.read B 0 = false) (gs : List Gate) :
    litValue (run gs B) 0 = false := by
  rw [litValue_eq_read, (run_extends _ _).2 _ (by simpa using hpos)]; simp [hB0]

theorem lit1 (hpos : 0 < B.size) (hB0 : Dag.read B 0 = false) (gs : List Gate) :
    litValue (run gs B) 1 = true := by
  rw [litValue_eq_read, show (1 : Nat) / 2 = 0 from rfl, (run_extends _ _).2 _ (by simpa using hpos)]; simp [hB0]

theorem Rw.emit_ok (n0 : Nat) (hn : B.size = n0) (st : Rw) (x y : Nat) :
    (st.emit n0 x y).2.map = st.map ∧
    Extends (run st.gates.toList B) (run (st.emit n0 x y).2.gates.toList B) ∧
    (st.emit n0 x y).1 / 2 < (run (st.emit n0 x y).2.gates.toList B).size ∧
    litValue (run (st.emit n0 x y).2.gates.toList B) (st.emit n0 x y).1 =
      (litValue (run st.gates.toList B) x && litValue (run st.gates.toList B) y) := by
  have e : run (st.emit n0 x y).2.gates.toList B = (run st.gates.toList B).push
      (litValue (run st.gates.toList B) x && litValue (run st.gates.toList B) y) := by
    simp [Rw.emit, run, List.foldl_append]
  have hs : (run st.gates.toList B).size = n0 + st.gates.size := by simp [hn]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [e]; exact extends_push _ _
  · rw [e]; simp [Rw.emit, hs]
  · rw [e]; simp only [Rw.emit]; rw [litValue_double, ← hs]
    unfold Dag.read; rw [Array.getElem?_push_size]; rfl

theorem Rw.and_ok (n0 : Nat) (hn : B.size = n0) (hpos : 0 < B.size) (hB0 : Dag.read B 0 = false) (st : Rw)
    (a b : Nat) (ha : a / 2 < (run st.gates.toList B).size) (hb : b / 2 < (run st.gates.toList B).size) :
    (st.and n0 a b).2.map = st.map ∧
    Extends (run st.gates.toList B) (run (st.and n0 a b).2.gates.toList B) ∧
    (st.and n0 a b).1 / 2 < (run (st.and n0 a b).2.gates.toList B).size ∧
    litValue (run (st.and n0 a b).2.gates.toList B) (st.and n0 a b).1 =
      (litValue (run st.gates.toList B) a && litValue (run st.gates.toList B) b) := by
  have hW : 0 < (run st.gates.toList B).size := by simp; omega
  have same : ∀ l : Nat, l / 2 < (run st.gates.toList B).size →
      litValue (run st.gates.toList B) l = (litValue (run st.gates.toList B) a && litValue (run st.gates.toList B) b) →
      ((l, st) : Nat × Rw).2.map = st.map ∧
      Extends (run st.gates.toList B) (run ((l, st) : Nat × Rw).2.gates.toList B) ∧
      ((l, st) : Nat × Rw).1 / 2 < (run ((l, st) : Nat × Rw).2.gates.toList B).size ∧
      litValue (run ((l, st) : Nat × Rw).2.gates.toList B) ((l, st) : Nat × Rw).1 =
        (litValue (run st.gates.toList B) a && litValue (run st.gates.toList B) b) :=
    fun l hl hv => ⟨rfl, extends_refl _, hl, hv⟩
  have v0 := lit0 hpos hB0 st.gates.toList
  have v1 := lit1 hpos hB0 st.gates.toList
  -- the ordered pair computes the same AND
  have hxy : (litValue (run st.gates.toList B) (min a b) && litValue (run st.gates.toList B) (max a b)) =
      (litValue (run st.gates.toList B) a && litValue (run st.gates.toList B) b) := by
    by_cases hab : a ≤ b
    · rw [Nat.min_eq_left hab, Nat.max_eq_right hab]
    · rw [Nat.min_eq_right (by omega), Nat.max_eq_left (by omega), Bool.and_comm]
  have hxb : min a b / 2 < (run st.gates.toList B).size := by
    by_cases hab : a ≤ b
    · rw [Nat.min_eq_left hab]; exact ha
    · rw [Nat.min_eq_right (by omega)]; exact hb
  have hyb : max a b / 2 < (run st.gates.toList B).size := by
    by_cases hab : a ≤ b
    · rw [Nat.max_eq_right hab]; exact hb
    · rw [Nat.max_eq_left (by omega)]; exact ha
  have emit := fun (h : True) => Rw.emit_ok n0 hn st (min a b) (max a b)
  unfold Rw.and
  split
  · rename_i h0
    apply same 0 (by simpa using hW)
    rcases h0 with h0 | h0 <;> subst h0 <;> simp [v0]
  split
  · rename_i _ h1
    subst h1; apply same b hb; simp [v1]
  split
  · rename_i _ _ h1
    subst h1; apply same a ha; simp [v1]
  split
  · rename_i _ _ _ h1
    subst h1; apply same a ha; simp
  split
  · rename_i _ _ _ _ h1
    subst h1; apply same 0 (by simpa using hW); rw [litValue_negLit, v0]; simp
  · simp only
    split
    · rename_i k _
      split
      · rename_i hh
        unfold Rw.hit at hh
        split at hh
        · rename_i hk
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh
          obtain ⟨⟨⟨hga, hgb⟩, hx⟩, hy⟩ := hh
          have hs : (run st.gates.toList B).size = n0 + st.gates.size := by simp [hn]
          apply same (2 * (n0 + k)) (by rw [hs]; omega)
          rw [litValue_double, ← hn, read_run_gate _ _ _ (by simpa using hk)]
          have hk' : (run (st.gates.toList.take k) B).size = n0 + k := by simp [hn]; omega
          simp only [Array.getElem_toList, hga, hgb]
          rw [← litValue_extends (run_take_extends _ _ k) _ (by rw [hk']; exact hx),
            ← litValue_extends (run_take_extends _ _ k) _ (by rw [hk']; exact hy), hxy]
        · cases hh
      · obtain ⟨h1, h2, h3, h4⟩ := emit trivial
        exact ⟨h1, h2, h3, h4.trans hxy⟩
    · obtain ⟨h1, h2, h3, h4⟩ := emit trivial
      exact ⟨h1, h2, h3, h4.trans hxy⟩

theorem Rw.step_ok (n0 : Nat) (hn : B.size = n0) (hpos : 0 < B.size) (hB0 : Dag.read B 0 = false)
    (live : Array Bool) (st : Rw) (V : Array Bool) (gt : Gate) (h : st.Ok B V) :
    (Rw.step n0 live st gt).Ok B (V.push (litValue V gt.a && litValue V gt.b)) := by
  have oldRead : ∀ x, x < V.size → Dag.read (V.push (litValue V gt.a && litValue V gt.b)) x = Dag.read V x := by
    intro x hx; simp [Dag.read, Array.getElem?_push, Nat.ne_of_lt hx]
  -- dropping the gate keeps every old entry
  have drop : ({ st with map := st.map.push none } : Rw).Ok B (V.push (litValue V gt.a && litValue V gt.b)) := by
    refine ⟨by simp [h.1], fun x l hx => ?_⟩
    simp only [Array.getElem?_push] at hx
    split at hx
    · cases hx
    · have hlt : x < st.map.size := by
        rcases Nat.lt_or_ge x st.map.size with h' | h'
        · exact h'
        · rw [Array.getElem?_eq_none (by omega)] at hx; cases hx
      obtain ⟨hb, hv⟩ := h.2 x l hx
      exact ⟨hb, by rw [hv, oldRead x (by rw [← h.1]; exact hlt)]⟩
  unfold Rw.step
  split
  · split
    · rename_i a b ha hb
      obtain ⟨hab, hav⟩ := Rw.lit_ok h ha
      obtain ⟨hbb, hbv⟩ := Rw.lit_ok h hb
      obtain ⟨hmap, hext, hlb, hlv⟩ := Rw.and_ok n0 hn hpos hB0 st a b hab hbb
      refine ⟨by simp [h.1], fun x l hx => ?_⟩
      simp only [Array.getElem?_push] at hx
      split at hx
      · rename_i hx'
        cases hx
        refine ⟨hlb, ?_⟩
        rw [hlv, hav, hbv, hx', h.1]; simp [Dag.read]
      · have hlt : x < st.map.size := by
          rcases Nat.lt_or_ge x st.map.size with h' | h'
          · exact h'
          · rw [Array.getElem?_eq_none (by omega)] at hx; cases hx
        obtain ⟨hb', hv'⟩ := h.2 x l hx
        exact ⟨Nat.lt_of_lt_of_le hb' hext.1,
          by rw [litValue_extends hext _ hb', hv', oldRead x (by rw [← h.1]; exact hlt)]⟩
    · exact drop
  · exact drop

theorem Rw.fold_ok (n0 : Nat) (hn : B.size = n0) (hpos : 0 < B.size) (hB0 : Dag.read B 0 = false)
    (live : Array Bool) (gs : List Gate) : ∀ (st : Rw) (V : Array Bool), st.Ok B V →
    (gs.foldl (Rw.step n0 live) st).Ok B (run gs V) := by
  induction gs with
  | nil => intro st V h; exact h
  | cons g gs ih =>
    intro st V h
    exact ih _ _ (Rw.step_ok n0 hn hpos hB0 live st V g h)

theorem Rw.start_ok (n0 : Nat) (hn : B.size = n0) : (Rw.start n0).Ok B B := by
  refine ⟨by simp [Rw.start, hn], fun x l hx => ?_⟩
  simp only [Rw.start, Array.getElem?_map, Array.getElem?_range] at hx
  split at hx
  · rename_i hx'
    simp only [Option.map_some, Option.some.injEq] at hx
    subst hx
    simp only [Rw.start, Array.toList_empty, run, List.foldl_nil]
    exact ⟨by omega, litValue_double _ _⟩
  · simp at hx

end

/-! ## Graph-level theorems -/

theorem Graph.values_run (g : Graph) (inputs state : Array Bool) :
    g.values inputs state = run g.gates.toList (#[false] ++ inputs ++ state) := by
  simp [Graph.values, run, ← Array.foldl_toList]

theorem Graph.rewrite_eval (g : Graph) (inputs state : Array Bool)
    (hi : inputs.size = g.inputs) (hs : state.size = g.latches) :
    g.rewrite.eval inputs state = g.eval inputs state := by
  let B := #[false] ++ inputs ++ state
  have hn : B.size = g.inputs + g.latches + 1 := by simp [B, hi, hs]; omega
  have hpos : 0 < B.size := by omega
  have hB0 : Dag.read B 0 = false := by simp [B, Dag.read, Array.getElem?_append]
  have hok := Rw.fold_ok _ hn hpos hB0 g.live g.gates.toList _ _ (Rw.start_ok _ hn)
  generalize hst : g.gates.toList.foldl (Rw.step (g.inputs + g.latches + 1) g.live)
    (Rw.start (g.inputs + g.latches + 1)) = st at hok
  have tr : ∀ l, (st.lit l).isSome = true →
      litValue (run st.gates.toList B) ((st.lit l).getD 0) = litValue (run g.gates.toList B) l := by
    intro l hl
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hl
    rw [hm]; exact (Rw.lit_ok hok hm).2
  unfold Graph.rewrite
  simp only [hst]
  split
  · rename_i hall
    simp only [Bool.and_eq_true, Array.all_eq_true] at hall
    split
    · simp only [Graph.eval, Graph.values_run]
      apply Prod.ext
      · apply Array.ext (by simp)
        intro k h1 h2
        simp only [Array.getElem_map]
        exact tr _ (hall.1 k (by simpa using h1))
      · apply Array.ext (by simp)
        intro k h1 h2
        simp only [Array.getElem_map]
        exact tr _ (hall.2 k (by simpa using h1))
    · rfl
  · rfl

theorem Graph.rewrite_wellFormed (g : Graph) (h : g.wellFormed = true) : g.rewrite.wellFormed = true := by
  unfold Graph.rewrite; dsimp only
  split
  · split
    · assumption
    · exact h
  · exact h

theorem Graph.rewrite_inputs (g : Graph) : g.rewrite.inputs = g.inputs := by
  unfold Graph.rewrite; dsimp only; split
  · split <;> rfl
  · rfl

theorem Graph.rewrite_latches (g : Graph) : g.rewrite.latches = g.latches := by
  unfold Graph.rewrite; dsimp only; split
  · split <;> rfl
  · rfl

theorem Graph.optimizeN_spec (n : Nat) : ∀ g : Graph,
    (g.optimizeN n).inputs = g.inputs ∧ (g.optimizeN n).latches = g.latches ∧
    (g.wellFormed = true → (g.optimizeN n).wellFormed = true) ∧
    (∀ inputs state, inputs.size = g.inputs → state.size = g.latches →
      (g.optimizeN n).eval inputs state = g.eval inputs state) := by
  induction n with
  | zero => intro g; exact ⟨rfl, rfl, id, fun _ _ _ _ => rfl⟩
  | succ n ih =>
    intro g
    simp only [Graph.optimizeN]
    have hr := And.intro (Graph.rewrite_inputs g) (Graph.rewrite_latches g)
    split
    · obtain ⟨h1, h2, h3, h4⟩ := ih g.rewrite
      refine ⟨h1.trans hr.1, h2.trans hr.2, fun h => h3 (g.rewrite_wellFormed h), fun ins st hi hs => ?_⟩
      rw [h4 ins st (by rw [hr.1]; exact hi) (by rw [hr.2]; exact hs), g.rewrite_eval ins st hi hs]
    · exact ⟨hr.1, hr.2, g.rewrite_wellFormed, fun ins st hi hs => g.rewrite_eval ins st hi hs⟩

/-- The optimised graph computes the same next state and outputs. -/
theorem Graph.optimize_eval (g : Graph) (inputs state : Array Bool)
    (hi : inputs.size = g.inputs) (hs : state.size = g.latches) :
    g.optimize.eval inputs state = g.eval inputs state :=
  (Graph.optimizeN_spec 8 g).2.2.2 inputs state hi hs

theorem Graph.optimize_wellFormed (g : Graph) (h : g.wellFormed = true) : g.optimize.wellFormed = true :=
  (Graph.optimizeN_spec 8 g).2.2.1 h

@[simp] theorem Graph.optimize_inputs (g : Graph) : g.optimize.inputs = g.inputs := (Graph.optimizeN_spec 8 g).1
@[simp] theorem Graph.optimize_latches (g : Graph) : g.optimize.latches = g.latches := (Graph.optimizeN_spec 8 g).2.1

theorem Graph.next_size_of_wellFormed (g : Graph) (h : g.wellFormed = true) : g.next.size = g.latches := by
  unfold Graph.wellFormed at h
  by_cases hne : g.next.size = g.latches
  · exact hne
  · have : (g.inputs == 0 || g.next.size != g.latches) = true := by simp [hne]
    simp [this] at h

end HDLean.Backend

namespace HDLean.Dag
open Backend

/-- Gate-count-preserving lowering followed by the proved AIG optimisation:
what every backend emits. -/
def lowerOpt (c : Dag d i r o) : Graph := (lowerTight c).optimize

theorem lowerOpt_correct (c : Dag d i r o) (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    (lowerOpt c).eval (xs.toArray.push rst) state.toArray =
      ((Vector.ofFn (c.nextState (fun k => state[k]) ((fun k => xs[k]), rst))).toArray,
       (Vector.ofFn (c.evalOutput (fun k => state[k]) (fun k => xs[k]))).toArray) := by
  unfold lowerOpt
  rw [Graph.optimize_eval _ _ _ (by simp [lowerTight]) (by simp [lowerTight]), lowerTight_correct]

theorem lowerOpt_wellFormed (c : Dag d i r o) : (lowerOpt c).wellFormed = true :=
  Graph.optimize_wellFormed _ (lowerTight_wellFormed c)

@[simp] theorem lowerOpt_next_size (c : Dag d i r o) : (lowerOpt c).next.size = (lowerOpt c).latches :=
  Graph.next_size_of_wellFormed _ (lowerOpt_wellFormed c)

end HDLean.Dag
