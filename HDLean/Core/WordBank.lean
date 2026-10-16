import HDLean.Core.Network
import HDLean.Core.Word

namespace HDLean

/-- Uniform finite register banks provide reusable bounded word indexing. -/
def bankWord (j : Fin count) : WordExpr d inputs (count * width) width :=
  Vector.ofFn fun k => .reg (flatIndex j k)

@[simp] theorem bankWord_inputs (j : Fin count) (s : Fin (count*width) → Bool)
    (xs ys : Fin inputs → Bool) :
    (bankWord j : WordExpr d inputs (count*width) width).eval xs s = (bankWord j : WordExpr d inputs (count*width) width).eval ys s := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [WordExpr.eval_bit _ _ _ k hk, WordExpr.eval_bit _ _ _ k hk]
  simp [bankWord, Expr.eval]

/-- Register-bank constructor with one bounded next-state word per entry. -/
def wordBank (name : String) (reset : Fin count → ResetKind)
    (words : Fin count → WordExpr d inputs (count*width) width)
    (outputs : Vector (Expr d inputs (count*width)) outBits) :
    Circuit d inputs (count*width) outBits where
  name := name
  state := (Vector.ofFn fun j : Fin count => Vector.ofFn fun k : Fin width =>
    ⟨s!"word_{j.val}_{k.val}", reset j, (words j)[k], ""⟩).flatten
  output := outputs

/-- Local word semantics of the physical constructor. ResetKind applies to each
bit, so resetting to true deliberately means an all-ones word. -/
theorem wordBank_next (name : String) (reset : Fin count → ResetKind)
    (words : Fin count → WordExpr d inputs (count*width) width) (outputs : Vector (Expr d inputs (count*width)) outBits) (s xs rst) (j : Fin count) :
    (bankWord j : WordExpr d inputs (count*width) width).eval xs
      ((wordBank name reset words outputs).next s (xs,rst)) =
      match reset j with
      | .unreset => (words j).eval xs s
      | .hold => if rst then (bankWord j : WordExpr d inputs (count*width) width).eval xs s else (words j).eval xs s
      | .synchronous b => if rst then if b then -1 else 0 else (words j).eval xs s := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [WordExpr.eval_bit _ _ _ k hk]
  simp only [bankWord, Vector.getElem_ofFn, Expr.eval, Circuit.next, wordBank]
  simp only [Fin.getElem_fin, Vector.getElem_flatten, Vector.getElem_ofFn, flatIndex_div, flatIndex_mod]
  change (match reset j with
    | .unreset => (words j)[k].eval xs s
    | .hold => if rst then s (flatIndex j ⟨k,hk⟩) else (words j)[k].eval xs s
    | .synchronous b => if rst then b else (words j)[k].eval xs s) = _
  cases reset j with
  | unreset => exact (WordExpr.eval_bit _ _ _ k hk).symm
  | hold =>
    cases rst <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact (WordExpr.eval_bit _ _ _ k hk).symm
    · simpa [bankWord, Expr.eval] using (WordExpr.eval_bit
        (bankWord j : WordExpr d inputs (count*width) width) xs s k hk).symm
  | synchronous b =>
    cases rst <;> cases b <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals first
      | exact (WordExpr.eval_bit _ _ _ k hk).symm
      | simp [BitVec.neg_one_eq_allOnes, hk]

end HDLean
