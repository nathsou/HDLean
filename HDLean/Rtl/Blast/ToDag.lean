import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas
import HDLean.Core.Dag

/-!
# From an and-inverter graph to a node graph

Each AIG declaration `g` becomes two nodes: `2g` carries its value and `2g+1`
its negation, so an AIG fanin (gate, inverter) is the node `2·gate + inverter`.
Atoms below `i` are inputs, the next `r` atoms are state bits.
-/
namespace HDLean.Rtl.Blast
open Std.Sat Std.Sat.AIG

/-- The node of a fanin. -/
def node (f : Fanin) : Nat := 2 * f.gate + (if f.invert then 1 else 0)

def atomOp (i r a : Nat) : Dag.Op 0 i r :=
  if h : a < i then .input ⟨a, h⟩ else if h' : a - i < r then .reg ⟨a - i, h'⟩ else .lit false

def declOps (i r g : Nat) : Decl Nat → List (Dag.Op 0 i r)
  | .false => [.lit false, .not (2 * g)]
  | .atom a => [atomOp i r a, .not (2 * g)]
  | .gate l r' => [.and (node l) (node r'), .not (2 * g)]

def opsFrom (i r : Nat) : Nat → List (Decl Nat) → List (Dag.Op 0 i r)
  | _, [] => []
  | g, d :: ds => declOps i r g d ++ opsFrom i r (g + 1) ds

def assignOf (i r : Nat) (xs : Fin i → Bool) (s : Fin r → Bool) (a : Nat) : Bool :=
  if h : a < i then xs ⟨a, h⟩ else if h' : a - i < r then s ⟨a - i, h'⟩ else false

/-- Denotation of a raw fanin, `false` when out of range. -/
def dn (aig : AIG Nat) (assign : Nat → Bool) (f : Fanin) : Bool :=
  if h : f.gate < aig.decls.size then ⟦aig, ⟨f.gate, f.invert, h⟩, assign⟧ else false

theorem denote_inv (aig : AIG Nat) (assign : Nat → Bool) (g : Nat) (inv : Bool) (h : g < aig.decls.size) :
    ⟦aig, ⟨g, inv, h⟩, assign⟧ = (⟦aig, ⟨g, false, h⟩, assign⟧ ^^ inv) := by
  simp [denote]

theorem opsFrom_length (i r : Nat) : ∀ (g : Nat) (ds : List (Decl Nat)), (opsFrom i r g ds).length = 2 * ds.length
  | _, [] => rfl
  | g, d :: ds => by
    cases d <;> simp [opsFrom, declOps, opsFrom_length i r (g + 1) ds] <;> omega

/-- Folding the nodes of declarations `g, g+1, ...` keeps the values of earlier
declarations at `2h` and their negations at `2h+1`. -/
theorem eval_opsFrom (aig : AIG Nat) (i r : Nat) (xs : Fin i → Bool) (s : Fin r → Bool) :
    ∀ (g : Nat) (acc : Array Bool), acc.size = 2 * g → ∀ (hg : g ≤ aig.decls.size),
      (∀ h (hh : h < g), acc[2 * h]? = some ⟦aig, ⟨h, false, by omega⟩, assignOf i r xs s⟧ ∧
        acc[2 * h + 1]? = some (!⟦aig, ⟨h, false, by omega⟩, assignOf i r xs s⟧)) →
      let res := Dag.evalNodes (opsFrom i r g (aig.decls.toList.drop g)) xs s acc
      res.size = 2 * aig.decls.size ∧
      ∀ h (hh : h < aig.decls.size), res[2 * h]? = some ⟦aig, ⟨h, false, hh⟩, assignOf i r xs s⟧ ∧
        res[2 * h + 1]? = some (!⟦aig, ⟨h, false, hh⟩, assignOf i r xs s⟧) := by
  intro g
  induction hn : aig.decls.size - g generalizing g with
  | zero =>
    intro acc hs hg hacc
    have hge : g = aig.decls.size := by omega
    subst hge
    simp only [List.drop_eq_nil_of_le (by simp : aig.decls.toList.length ≤ aig.decls.size), opsFrom]
    exact ⟨by simpa using hs, fun h hh => hacc h hh⟩
  | succ n ih =>
    intro acc hs hg hacc
    have hlt : g < aig.decls.size := by omega
    have hdrop : aig.decls.toList.drop g = aig.decls[g] :: aig.decls.toList.drop (g + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [Array.length_toList]; exact hlt)]
      simp
    rw [hdrop]
    simp only [opsFrom, Dag.evalNodes, List.foldl_append]
    have hread : ∀ (f : Fanin) (hf : f.gate < g),
        Dag.read acc (node f) = ⟦aig, ⟨f.gate, f.invert, by omega⟩, assignOf i r xs s⟧ := by
      intro f hf
      have := hacc f.gate hf
      rw [denote_inv]
      cases hinv : f.invert
      · simp only [node, hinv, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Dag.read, this.1,
          Option.getD_some, Bool.xor_false]
      · simp only [node, hinv, ↓reduceIte, Dag.read, this.2, Option.getD_some, Bool.xor_true]
    have hnot : ∀ v : Bool, Dag.read (acc.push v) (2 * g) = v := by
      intro v; simp only [Dag.read, Array.getElem?_push, hs, ↓reduceIte, Option.getD_some]
    have hcases : ∀ d, aig.decls[g] = d →
        (declOps i r g d).foldl (fun values op => values.push (op.eval xs s (Dag.read values))) acc =
        (acc.push ⟦aig, ⟨g, false, hlt⟩, assignOf i r xs s⟧).push (!⟦aig, ⟨g, false, hlt⟩, assignOf i r xs s⟧) := by
      intro d hd
      cases d with
      | false =>
        simp only [declOps, List.foldl_cons, List.foldl_nil]
        rw [denote_idx_false hd]
        simp only [Dag.Op.eval, hnot]
      | atom a =>
        simp only [declOps, List.foldl_cons, List.foldl_nil]
        have hat : Dag.Op.eval xs s (Dag.read acc) (atomOp i r a) = assignOf i r xs s a := by
          unfold atomOp assignOf
          split
          · rfl
          · split <;> rfl
        rw [hat, denote_idx_atom hd]
        simp only [Dag.Op.eval, hnot, Bool.xor_false]
      | gate l r' =>
        have hd' := aig.hdag hlt hd
        simp only [declOps, List.foldl_cons, List.foldl_nil]
        rw [denote_idx_gate hd]
        simp only [Dag.Op.eval, hnot, hread l hd'.1, hread r' hd'.2, Bool.xor_false]
    rw [hcases _ rfl]
    refine ih (g + 1) (by omega) _ (by simp [hs]; omega) (by omega) ?_
    · intro h hh
      by_cases hhg : h < g
      · have := hacc h hhg
        have h1 : ¬ (2 * h = 2 * g + 1) := by omega
        have h2 : ¬ (2 * h = 2 * g) := by omega
        have h3 : ¬ (2 * h + 1 = 2 * g + 1) := by omega
        have h4 : ¬ (2 * h + 1 = 2 * g) := by omega
        simp only [Array.getElem?_push, Array.size_push, hs, h1, h2, h3, h4, ↓reduceIte]
        exact this
      · have hhe : h = g := by omega
        subst hhe
        have h1 : ¬ (2 * h = 2 * h + 1) := by omega
        simp only [Array.getElem?_push, Array.size_push, hs, h1, ↓reduceIte]
        simp


theorem eval_aig (aig : AIG Nat) (i r : Nat) (xs : Fin i → Bool) (s : Fin r → Bool) (f : Fanin)
    (hf : f.gate < aig.decls.size) :
    Dag.read (Dag.evalNodes (opsFrom i r 0 aig.decls.toList) xs s) (node f) =
      ⟦aig, ⟨f.gate, f.invert, hf⟩, assignOf i r xs s⟧ := by
  have := (eval_opsFrom aig i r xs s 0 #[] rfl (Nat.zero_le _) (fun h hh => absurd hh (Nat.not_lt_zero _))).2
    f.gate hf
  simp only [List.drop_zero] at this
  rw [denote_inv]
  cases hinv : f.invert
  · simp only [node, hinv, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Dag.read, this.1, Option.getD_some,
      Bool.xor_false]
  · simp only [node, hinv, ↓reduceIte, Dag.read, this.2, Option.getD_some, Bool.xor_true]

/-- The node graph of an AIG with the given next-state and output fanins. -/
def toDag (name : String) (aig : AIG Nat) (i r o : Nat) (next : Vector Fanin r) (out : Vector Fanin o)
    (reset : Vector ResetKind r) : Option (Dag 0 i r o) :=
  if h : Dag.WellFormed (opsFrom i r 0 aig.decls.toList) (next.map node) (out.map node) then
    some { name := name, nodes := opsFrom i r 0 aig.decls.toList, next := next.map node, out := out.map node,
           reset := reset, wf := h }
  else none

private theorem gate_lt (aig : AIG Nat) (i r : Nat) (f : Fanin)
    (h : node f < (opsFrom i r 0 aig.decls.toList).length) : f.gate < aig.decls.size := by
  rw [opsFrom_length] at h
  simp only [node, Array.length_toList] at h
  split at h <;> omega

theorem toDag_nextState {name : String} {aig : AIG Nat} {i r o : Nat} {next : Vector Fanin r}
    {out : Vector Fanin o} {reset : Vector ResetKind r} {dag : Dag 0 i r o}
    (h : toDag name aig i r o next out reset = some dag) (s : Fin r → Bool) (xs : Fin i → Bool) (rst : Bool)
    (k : Fin r) :
    dag.nextState s (xs, rst) k = Dag.resetValue reset[k] (s k) (dn aig (assignOf i r xs s) next[k]) rst := by
  unfold toDag at h
  split at h
  · rename_i hwf
    cases h
    have hb : node next[k.val] < (opsFrom i r 0 aig.decls.toList).length := by
      simpa using hwf.2.1 k
    have hg := gate_lt aig i r _ hb
    simp only [Dag.nextState, Dag.values, Fin.getElem_fin, Vector.getElem_map]
    rw [eval_aig aig i r xs s _ hg]
    simp [dn, hg]
  · cases h

theorem toDag_evalOutput {name : String} {aig : AIG Nat} {i r o : Nat} {next : Vector Fanin r}
    {out : Vector Fanin o} {reset : Vector ResetKind r} {dag : Dag 0 i r o}
    (h : toDag name aig i r o next out reset = some dag) (s : Fin r → Bool) (xs : Fin i → Bool) (k : Fin o) :
    dag.evalOutput s xs k = dn aig (assignOf i r xs s) out[k] := by
  unfold toDag at h
  split at h
  · rename_i hwf
    cases h
    have hb : node out[k.val] < (opsFrom i r 0 aig.decls.toList).length := by
      simpa using hwf.2.2 k
    have hg := gate_lt aig i r _ hb
    simp only [Dag.evalOutput, Dag.values, Fin.getElem_fin, Vector.getElem_map]
    rw [eval_aig aig i r xs s _ hg]
    simp [dn, hg]
  · cases h

end HDLean.Rtl.Blast
