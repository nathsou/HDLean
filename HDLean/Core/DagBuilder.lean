import HDLean.Core.Dag

set_option backward.isDefEq.respectTransparency false

namespace HDLean.Dag.Build

/-- The reverse list makes allocation constant time in the logical representation.
Only `finish` reverses the completed list. No semantic table or hash cache exists. -/
structure State (d : Domain) (i r : Nat) where
  count : Nat
  reversed : List (Op d i r)
  length_eq : reversed.length = count
  wf : NodesWF 0 reversed.reverse

def empty : State d i r := ⟨0, [], rfl, trivial⟩

abbrev M (d : Domain) (i r : Nat) := StateT (State d i r) Option
abbrev Ref := Nat
abbrev Word (w : Nat) := Vector Ref w

/-- A rejected reference never enters the intrinsically well-formed state. -/
def emit (op : Op d i r) : M d i r Ref := fun s =>
  if h : op.Valid s.count then
    some (s.count, ⟨s.count+1, op::s.reversed, by simp [s.length_eq], by
      rw [List.reverse_cons]
      exact nodesWF_snoc s.wf (by simpa [s.length_eq] using h)⟩)
  else none

def literal (b : Bool) : M d i r Ref := emit (.lit b)
def input (k : Fin i) : M d i r Ref := emit (.input k)
def reg (k : Fin r) : M d i r Ref := emit (.reg k)
def inv (a : Ref) : M d i r Ref := emit (.not a)
def and (a b : Ref) : M d i r Ref := emit (.and a b)
def xor (a b : Ref) : M d i r Ref := emit (.xor a b)
def mux (c a b : Ref) : M d i r Ref := emit (.mux c a b)
def or (a b : Ref) : M d i r Ref := do
  let na ← inv a
  let nb ← inv b
  inv (← and na nb)

/-- Collect fixed-width results using a list, avoiding logical `Array.push`. -/
def tabulateList (f : Fin n → M d i r α) : (k : Nat) → k ≤ n → M d i r (List α)
  | 0, _ => pure []
  | k+1, h => do
    let a ← f ⟨n-(k+1), by omega⟩
    let tail ← tabulateList f k (by omega)
    pure (a::tail)

theorem tabulateList_length (f : Fin n → M d i r α) (k : Nat) (hk : k ≤ n)
    (s t : State d i r) (xs : List α) (h : tabulateList f k hk s = some (xs,t)) : xs.length = k := by
  induction k generalizing s xs with
  | zero => simp [tabulateList, pure, StateT.pure] at h; rcases h with ⟨rfl,rfl⟩; rfl
  | succ k ih =>
    simp only [tabulateList, bind, StateT.bind] at h
    cases hf : f ⟨n-(k+1),by omega⟩ s with
    | none => simp [hf] at h
    | some p =>
      rcases p with ⟨a,s'⟩
      simp only [hf, Option.bind_some] at h
      cases ht : tabulateList f k (by omega) s' with
      | none => simp [ht] at h
      | some q =>
        rcases q with ⟨ys,t'⟩
        simp [ht, pure, StateT.pure] at h
        rcases h with ⟨rfl,rfl⟩
        simp [ih _ _ _ ht]

def tabulate (f : Fin n → M d i r α) : M d i r (Vector α n) := fun s =>
  match h : tabulateList f n (Nat.le_refl n) s with
  | none => none
  | some (xs,t) => some (⟨xs.toArray, by simpa using tabulateList_length f n (Nat.le_refl n) s t xs h⟩,t)

def finish (name : String) (next : Vector Ref r) (out : Vector Ref o)
    (reset : Vector ResetKind r) (s : State d i r) : Option (Dag d i r o) :=
  if hn : ∀ k : Fin r, next[k] < s.count then
    if ho : ∀ k : Fin o, out[k] < s.count then
      some { name := name
             nodes := s.reversed.reverse
             next := next
             out := out
             reset := reset
             wf := ⟨s.wf, by simpa [s.length_eq] using hn, by simpa [s.length_eq] using ho⟩ }
    else none
  else none

/-- `run` is fail closed on malformed references; accepted circuits carry their
backwards-reference proof rather than rechecking semantics after lowering. -/
def run (name : String) (reset : Vector ResetKind r)
    (program : M d i r (Vector Ref r × Vector Ref o)) : Option (Dag d i r o) := do
  let ((next,out),s) ← program empty
  finish name next out reset s

theorem emit_count (op : Op d i r) (s t : State d i r) (j : Ref)
    (h : emit op s = some (j,t)) : j = s.count ∧ t.count = s.count+1 := by
  simp only [emit] at h
  split at h
  · cases h; exact ⟨rfl,rfl⟩
  · contradiction

theorem emit_nodes (op : Op d i r) (s t : State d i r) (j : Ref)
    (h : emit op s = some (j,t)) : t.reversed.reverse = s.reversed.reverse ++ [op] := by
  simp only [emit] at h
  split at h
  · cases h; simp
  · contradiction

def State.values (s : State d i r) (xs : Fin i → Bool) (regs : Fin r → Bool) : Array Bool :=
  evalNodes s.reversed.reverse xs regs

@[simp] theorem State.values_size (s : State d i r) (xs regs) :
    (s.values xs regs).size = s.count := by simp [State.values, s.length_eq]

theorem emit_values (op : Op d i r) (s t : State d i r) (j : Ref)
    (h : emit op s = some (j,t)) (xs regs) :
    t.values xs regs = (s.values xs regs).push (op.eval xs regs (read (s.values xs regs))) := by
  unfold State.values
  rw [emit_nodes op s t j h]
  simp [evalNodes, List.foldl_append]

theorem emit_value (op : Op d i r) (s t : State d i r) (j : Ref)
    (h : emit op s = some (j,t)) (xs regs) :
    read (t.values xs regs) j = op.eval xs regs (read (s.values xs regs)) := by
  rw [emit_values op s t j h, (emit_count op s t j h).1]
  rw [← s.values_size xs regs]
  simp only [read, Array.getElem?_push, ite_true, Option.getD_some]

theorem emit_preserves (op : Op d i r) (s t : State d i r) (j k : Ref)
    (h : emit op s = some (j,t)) (hk : k < s.count) (xs regs) :
    read (t.values xs regs) k = read (s.values xs regs) k := by
  rw [emit_values op s t j h]
  simp [read, Array.getElem?_push, Nat.ne_of_lt hk]

/-- A proof-only interpretation into the existing expression language. This is
never used to construct or lower a DAG. -/
def opExpression (env : Nat → Expr d i r) : Op d i r → Expr d i r
  | .lit b => .lit b | .input k => .input k | .reg k => .reg k
  | .not a => .inv (env a) | .and a b => .and (env a) (env b)
  | .xor a b => .xor (env a) (env b) | .mux c a b => .mux (env c) (env a) (env b)

def expressionRead (v : Array (Expr d i r)) (j : Nat) : Expr d i r := v[j]?.getD (.lit false)
def expressionFold (nodes : List (Op d i r)) (v : Array (Expr d i r) := #[]) : Array (Expr d i r) :=
  nodes.foldl (fun v op => v.push (opExpression (expressionRead v) op)) v

def State.expressions (s : State d i r) : Array (Expr d i r) := expressionFold s.reversed.reverse
def State.expression (s : State d i r) (j : Ref) : Expr d i r := expressionRead s.expressions j

@[simp] theorem expressionFold_size (nodes : List (Op d i r)) (v : Array (Expr d i r)) :
    (expressionFold nodes v).size = v.size+nodes.length := by
  induction nodes generalizing v with
  | nil => simp [expressionFold]
  | cons op nodes ih =>
    change (expressionFold nodes (v.push (opExpression (expressionRead v) op))).size = _
    rw [ih]; simp; omega
@[simp] theorem State.expressions_size (s : State d i r) : s.expressions.size = s.count := by
  simp [State.expressions, s.length_eq]

theorem emit_expressions (op : Op d i r) (s t : State d i r) (j : Ref)
    (h : emit op s = some (j,t)) :
    t.expressions = s.expressions.push (opExpression s.expression op) := by
  unfold State.expressions
  rw [emit_nodes op s t j h]
  simp only [expressionFold, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem emit_expression (op : Op d i r) (s t : State d i r) (j : Ref)
    (h : emit op s = some (j,t)) : t.expression j = opExpression s.expression op := by
  unfold State.expression
  rw [emit_expressions op s t j h, (emit_count op s t j h).1, ← s.expressions_size]
  simp only [expressionRead, Array.getElem?_push, ite_true, Option.getD_some]
  rfl

theorem emit_expression_preserves (op : Op d i r) (s t : State d i r) (j k : Ref)
    (h : emit op s = some (j,t)) (hk : k < s.count) : t.expression k = s.expression k := by
  unfold State.expression
  rw [emit_expressions op s t j h]
  simp [expressionRead, Array.getElem?_push, Nat.ne_of_lt hk]

/-- The compositional specification for builder programs. All prior references
retain their meaning, and newly returned references carry an expression spec. -/
def Extends (s t : State d i r) : Prop :=
  s.count ≤ t.count ∧ ∀ k, k < s.count → t.expression k = s.expression k

theorem extends_refl (s : State d i r) : Extends s s := ⟨Nat.le_refl _,fun _ _ => rfl⟩
theorem extends_trans (h : Extends s t) (h' : Extends t u) : Extends s u :=
  ⟨Nat.le_trans h.1 h'.1, fun k hk => (h'.2 k (Nat.lt_of_lt_of_le hk h.1)).trans (h.2 k hk)⟩

def Refines (s : State d i r) (j : Ref) (e : Expr d i r) : Prop :=
  j < s.count ∧ s.expression j = e

def WordRefines (s : State d i r) (js : Word w) (es : WordExpr d i r w) : Prop :=
  ∀ k : Fin w, Refines s js[k] es[k]

theorem Refines.mono (h : Refines s j e) (hx : Extends s t) : Refines t j e :=
  ⟨Nat.lt_of_lt_of_le h.1 hx.1, (hx.2 j h.1).trans h.2⟩
theorem WordRefines.mono (h : WordRefines s js es) (hx : Extends s t) : WordRefines t js es :=
  fun k => (h k).mono hx

def Ensures (s : State d i r) (m : M d i r α) (post : α → State d i r → Prop) : Prop :=
  ∃ a t, m s = some (a,t) ∧ Extends s t ∧ post a t

theorem ensures_pure (s : State d i r) (a : α) (h : post a s) : Ensures s (pure a) post :=
  ⟨a,s,rfl,extends_refl s,h⟩
theorem ensures_bind (h : Ensures s m p)
    (k : ∀ a t, Extends s t → p a t → Ensures t (f a) q) : Ensures s (m >>= f) q := by
  obtain ⟨a,t,hm,he,hp⟩ := h
  obtain ⟨b,u,hf,he',hq⟩ := k a t he hp
  exact ⟨b,u,by simp [bind,StateT.bind,hm,hf],extends_trans he he',hq⟩

theorem emit_ensures (op : Op d i r) (s : State d i r) (hv : op.Valid s.count) :
    Ensures s (emit op) (fun j t => Refines t j (opExpression s.expression op)) := by
  let t : State d i r := ⟨s.count+1,op::s.reversed,by simp [s.length_eq],by
    rw [List.reverse_cons]; exact nodesWF_snoc s.wf (by simpa [s.length_eq] using hv)⟩
  have h : emit op s = some (s.count,t) := by simp [emit,hv,t]
  exact ⟨s.count,t,h,⟨by simp [t],fun k hk => emit_expression_preserves op s t _ k h hk⟩,
    ⟨by simp [t],emit_expression op s t _ h⟩⟩

theorem literal_ensures (s : State d i r) (b : Bool) :
    Ensures s (literal b) (fun j t => Refines t j (.lit b)) := emit_ensures _ _ trivial

theorem reg_ensures (s : State d i r) (k : Fin r) :
    Ensures s (reg k) (fun j t => Refines t j (.reg k)) := emit_ensures _ _ trivial

theorem inv_ensures (ha : Refines s a ea) :
    Ensures s (inv a) (fun j t => Refines t j (.inv ea)) := by
  simpa only [inv,opExpression,ha.2] using emit_ensures (.not a) s ha.1

theorem and_ensures (ha : Refines s a ea) (hb : Refines s b eb) :
    Ensures s (and a b) (fun j t => Refines t j (.and ea eb)) := by
  simpa only [and,opExpression,ha.2,hb.2] using emit_ensures (.and a b) s ⟨ha.1,hb.1⟩

theorem xor_ensures (ha : Refines s a ea) (hb : Refines s b eb) :
    Ensures s (xor a b) (fun j t => Refines t j (.xor ea eb)) := by
  simpa only [xor,opExpression,ha.2,hb.2] using emit_ensures (.xor a b) s ⟨ha.1,hb.1⟩

theorem mux_ensures (hc : Refines s c ec) (ha : Refines s a ea) (hb : Refines s b eb) :
    Ensures s (mux c a b) (fun j t => Refines t j (.mux ec ea eb)) := by
  simpa only [mux,opExpression,hc.2,ha.2,hb.2] using emit_ensures (.mux c a b) s ⟨hc.1,ha.1,hb.1⟩

theorem or_ensures (ha : Refines s a ea) (hb : Refines s b eb) :
    Ensures s (or a b) (fun j t => Refines t j (ea.or eb)) := by
  apply ensures_bind (inv_ensures ha)
  intro na t he hna
  apply ensures_bind (inv_ensures (hb.mono he))
  intro nb u he' hnb
  apply ensures_bind (and_ensures (hna.mono he') hnb)
  intro ab v he'' hab
  exact inv_ensures hab

theorem ensures_weaken (h : Ensures s m p) (hp : ∀ a t, p a t → q a t) : Ensures s m q := by
  obtain ⟨a,t,hm,he,h⟩ := h
  exact ⟨a,t,hm,he,hp a t h⟩

theorem tabulateList_ensures (f : Fin n → M d i r α)
    (P : Fin n → α → State d i r → Prop)
    (mono : ∀ k a s t, Extends s t → P k a s → P k a t)
    (s : State d i r)
    (h : ∀ t, Extends s t → ∀ k, Ensures t (f k) (P k))
    (count : Nat) (hc : count ≤ n) :
    Ensures s (tabulateList f count hc) (fun xs t =>
      ∃ hl : xs.length = count, ∀ j : Fin count,
        P ⟨n-count+j.val,by omega⟩ (xs[j.val]'(by omega)) t) := by
  induction count generalizing s with
  | zero =>
    apply ensures_pure
    exact ⟨rfl,fun j => Fin.elim0 j⟩
  | succ count ih =>
    apply ensures_bind (h s (extends_refl s) ⟨n-(count+1),by omega⟩)
    intro a t he ha
    apply ensures_bind (ih t (fun u hu k => h u (extends_trans he hu) k) (by omega))
    intro tail u he' ht
    apply ensures_pure
    obtain ⟨hl,hp⟩ := ht
    refine ⟨by simp [hl],?_⟩
    intro j
    rcases j with ⟨j,hj⟩
    cases j with
    | zero =>
      simpa only [Nat.add_zero,List.getElem_cons_zero] using mono _ a t u he' ha
    | succ k =>
      have hk : k < count := by omega
      have hx := hp ⟨k,hk⟩
      have heq : n-(count+1)+(k+1) = n-count+k := by omega
      simpa only [List.getElem_cons_succ,heq] using hx

theorem tabulate_ensures (f : Fin n → M d i r α)
    (P : Fin n → α → State d i r → Prop)
    (mono : ∀ k a s t, Extends s t → P k a s → P k a t)
    (s : State d i r)
    (h : ∀ t, Extends s t → ∀ k, Ensures t (f k) (P k)) :
    Ensures s (tabulate f) (fun xs t => ∀ k : Fin n, P k xs[k] t) := by
  obtain ⟨xs,t,hm,he,hl,hp⟩ := tabulateList_ensures f P mono s h n (Nat.le_refl n)
  refine ⟨⟨xs.toArray,by simpa using hl⟩,t,?_,he,?_⟩
  · simp only [tabulate]
    split
    · rename_i hnone; rw [hm] at hnone; contradiction
    · rename_i ys u hu
      have eq := Option.some.inj (hu.symm.trans hm)
      cases eq
      rfl
  · intro k
    simpa using hp k

theorem expressionRead_eval (v : Array (Expr d i r)) (k : Nat) (xs regs) :
    (expressionRead v k).eval xs regs = read (v.map (Expr.eval xs regs)) k := by
  simp only [expressionRead,read,Array.getElem?_map]
  cases v[k]? <;> rfl

theorem opExpression_eval (env : Nat → Expr d i r) (op : Op d i r) (xs regs) :
    (opExpression env op).eval xs regs = op.eval xs regs (fun k => (env k).eval xs regs) := by
  cases op <;> rfl

theorem expressionFold_eval (nodes : List (Op d i r)) (v : Array (Expr d i r)) (xs regs) :
    (expressionFold nodes v).map (Expr.eval xs regs) =
      evalNodes nodes xs regs (v.map (Expr.eval xs regs)) := by
  induction nodes generalizing v with
  | nil => rfl
  | cons op nodes ih =>
    change (expressionFold nodes (v.push (opExpression (expressionRead v) op))).map _ = _
    rw [ih]
    simp only [Array.map_push,opExpression_eval,expressionRead_eval]
    rfl

theorem State.expression_eval (s : State d i r) (j : Ref) (xs regs) :
    (s.expression j).eval xs regs = read (s.values xs regs) j := by
  rw [State.expression,expressionRead_eval]
  unfold State.expressions
  rw [expressionFold_eval]
  simp only [Array.map_empty]
  rfl

theorem Refines.eval (h : Refines s j e) (xs regs) :
    read (s.values xs regs) j = e.eval xs regs := by
  rw [← s.expression_eval, h.2]

/-- Compositional builder proofs can reuse any existing circuit refinement. The
hypothesis relates only returned references; it is proved once from primitive
allocation laws, not by reducing a whole concrete circuit validator. -/
theorem run_implements (c : Circuit d i r o)
    (program : M d i r (Vector Ref r × Vector Ref o))
    (h : Ensures empty program (fun p t =>
      (∀ k : Fin r, Refines t p.1[k] c.state[k].next) ∧ WordRefines t p.2 c.output)) :
    ∃ dag, run c.name (c.state.map (·.reset)) program = some dag ∧
      (∀ s xs, dag.nextState s xs = c.next s xs) ∧
      (∀ s xs, dag.evalOutput s xs = c.evalOutput s xs) := by
  obtain ⟨⟨next,out⟩,t,hm,he,hn,ho⟩ := h
  have hnext : ∀ k : Fin r, next[k] < t.count := fun k => (hn k).1
  have hout : ∀ k : Fin o, out[k] < t.count := fun k => (ho k).1
  let dag : Dag d i r o := {
    name := c.name
    nodes := t.reversed.reverse
    next := next
    out := out
    reset := c.state.map (·.reset)
    wf := ⟨t.wf,by simpa [t.length_eq] using hnext,by simpa [t.length_eq] using hout⟩ }
  refine ⟨dag,?_,?_,?_⟩
  · simp [run,hm,finish,hnext,hout,dag]
    exact ⟨hnext,hout⟩
  · intro s xs
    funext k
    have hh := (hn k).eval xs.1 s
    change resetValue (c.state.map (·.reset))[k] (s k)
      (read (t.values xs.1 s) next[k]) xs.2 = _
    rw [hh]
    simp only [Fin.getElem_fin,Vector.getElem_map]
    cases hk : c.state[k.val].reset <;> simp [resetValue,Circuit.next,hk]
  · intro s xs
    funext k
    exact (ho k).eval xs s

end HDLean.Dag.Build
