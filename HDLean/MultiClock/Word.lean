import HDLean.Core.Word
import HDLean.Semantics.Clock
namespace HDLean.WordExpr

def shiftRight (a : WordExpr d i r w) (n : Nat) : WordExpr d i r w :=
  Vector.ofFn fun j => if h : n+j.val < w then a[n+j.val] else .lit false

@[simp] theorem shiftRight_correct (a : WordExpr d i r w) (n : Nat) (xs state) :
    (shiftRight a n).eval xs state = a.eval xs state >>> n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [eval_bit _ _ _ j hj, BitVec.getLsbD_ushiftRight]
  by_cases h : n+j < w
  · simp only [shiftRight, Vector.getElem_ofFn, h, ↓reduceDIte]
    exact (eval_bit a xs state (n+j) h).symm
  · simp [shiftRight, h, Expr.eval, BitVec.getLsbD_of_ge (a.eval xs state) (n+j) (by omega)]

def gray (a : WordExpr d i r w) : WordExpr d i r w := bitXor a (shiftRight a 1)
@[simp] theorem gray_correct (a : WordExpr d i r w) (xs state) :
    (gray a).eval xs state = HDLean.gray (a.eval xs state) := by
  simp [gray, HDLean.gray]

def ungray (a : WordExpr d i r w) : WordExpr d i r w :=
  (List.range w).foldl (fun acc j => bitXor acc (shiftRight a j)) (literal 0)

@[simp] theorem ungray_correct (a : WordExpr d i r w) (xs state) :
    (ungray a).eval xs state =
      (List.range w).foldl (fun acc j => acc ^^^ (a.eval xs state >>> j)) 0 := by
  have h : ∀ (ls : List Nat) (acc : WordExpr d i r w),
      (ls.foldl (fun acc j => bitXor acc (shiftRight a j)) acc).eval xs state =
      ls.foldl (fun acc j => acc ^^^ (a.eval xs state >>> j)) (acc.eval xs state) := by
    intro ls
    induction ls with
    | nil => simp
    | cons n ns ih => intro acc; simpa using ih (bitXor acc (shiftRight a n))
  simpa [ungray] using h (List.range w) (literal 0)
end HDLean.WordExpr
