import HDLean.Core.DagBuilder

namespace HDLean.Dag.Build

theorem valid_mono (op : Op d i r) (h : op.Valid n) (hn : n ≤ m) : op.Valid m := by
  cases op <;> simp_all [Op.Valid] <;> omega

theorem nodesWF_of_valid (ops : List (Op d i r)) (h : ∀ op ∈ ops, op.Valid n) :
    NodesWF n ops := by
  induction ops generalizing n with
  | nil => trivial
  | cons op ops ih =>
    exact ⟨h op (by simp), ih (fun a ha => valid_mono a (h a (by simp [ha])) (by omega))⟩

/-- Allocate an independent block in one reverse-list update. Each operand is
checked against the state before the block, so allocation preserves sharing. -/
def extendBlock (s : State d i r) (ops : List (Op d i r))
    (h : ∀ op ∈ ops, op.Valid s.count) : State d i r where
  count := s.count + ops.length
  reversed := ops.reverse ++ s.reversed
  length_eq := by simp [s.length_eq, Nat.add_comm]
  wf := by
    simp only [List.reverse_append, List.reverse_reverse]
    apply (nodesWF_append _ _ _).2
    exact ⟨s.wf, by simpa [s.length_eq] using nodesWF_of_valid ops h⟩

def emitBlock (f : Fin w → Op d i r) : M d i r (Fin w → Ref) := fun s =>
  let ops := List.ofFn f
  if h : ops.all (fun op => decide (op.Valid s.count)) = true then
    some (fun k => s.count + k.val, extendBlock s ops (by simpa using h))
  else none

def emitWord (f : Fin w → Op d i r) : M d i r (Word w) := do
  let refs ← emitBlock f
  pure (Vector.ofFn refs)

theorem opExpression_append (op : Op d i r) (v extra : Array (Expr d i r))
    (h : op.Valid v.size) :
    opExpression (expressionRead (v ++ extra)) op = opExpression (expressionRead v) op := by
  cases op <;> simp_all [Op.Valid, opExpression, expressionRead, Array.getElem?_append_left]

theorem expressionFold_independent (ops : List (Op d i r)) (v : Array (Expr d i r))
    (h : ∀ op ∈ ops, op.Valid v.size) :
    expressionFold ops v = v ++ (ops.map (opExpression (expressionRead v))).toArray := by
  induction ops generalizing v with
  | nil => simp [expressionFold]
  | cons op ops ih =>
    change expressionFold ops (v.push (opExpression (expressionRead v) op)) = _
    rw [ih _ (fun a ha => valid_mono a (h a (by simp [ha])) (by simp))]
    have hm : ops.map (opExpression (expressionRead (v.push (opExpression (expressionRead v) op)))) =
        ops.map (opExpression (expressionRead v)) := by
      apply List.map_congr_left
      intro a ha
      simpa only [Array.push_eq_append] using opExpression_append a v #[opExpression (expressionRead v) op] (h a (by simp [ha]))
    rw [hm]
    rw [List.map_cons, List.toArray_cons, Array.push_eq_append, Array.append_assoc]

theorem extendBlock_expressions (s : State d i r) (ops : List (Op d i r))
    (h : ∀ op ∈ ops, op.Valid s.count) :
    (extendBlock s ops h).expressions = s.expressions ++ (ops.map (opExpression s.expression)).toArray := by
  change expressionFold (ops.reverse ++ s.reversed).reverse = _
  simp only [List.reverse_append, List.reverse_reverse, expressionFold, List.foldl_append]
  exact expressionFold_independent ops s.expressions (by simpa using h)

theorem extendBlock_extends (s : State d i r) (ops : List (Op d i r))
    (h : ∀ op ∈ ops, op.Valid s.count) : Extends s (extendBlock s ops h) := by
  refine ⟨by simp [extendBlock], fun k hk => ?_⟩
  unfold State.expression
  rw [extendBlock_expressions]
  simp only [expressionRead, Array.getElem?_append_left (show k < s.expressions.size by simpa using hk)]

theorem emitBlock_ensures (s : State d i r) (f : Fin w → Op d i r)
    (h : ∀ k, (f k).Valid s.count) :
    Ensures s (emitBlock f) (fun refs t => ∀ k, Refines t (refs k) (opExpression s.expression (f k))) := by
  have hv : ∀ op ∈ List.ofFn f, op.Valid s.count := by simpa using h
  refine ⟨(fun k => s.count + k.val), extendBlock s (List.ofFn f) hv, ?_, extendBlock_extends _ _ _, ?_⟩
  · simp [emitBlock, hv]
  · intro k
    refine ⟨by simp [extendBlock], ?_⟩
    unfold State.expression
    rw [extendBlock_expressions]
    simp [expressionRead, s.expressions_size]
    rfl

theorem emitWord_ensures (s : State d i r) (f : Fin w → Op d i r)
    (h : ∀ k, (f k).Valid s.count) :
    Ensures s (emitWord f) (fun refs t => ∀ k : Fin w,
      Refines t refs[k] (opExpression s.expression (f k))) := by
  apply ensures_bind (emitBlock_ensures s f h)
  intro refs t _ hr
  exact ensures_pure t _ (by simpa using hr)

end HDLean.Dag.Build
