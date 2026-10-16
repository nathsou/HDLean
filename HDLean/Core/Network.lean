import HDLean.Core.Circuit

namespace HDLean

/-- Row-major addressing for a finite collection of module state or port vectors. -/
def flatIndex (row : Fin m) (column : Fin n) : Fin (m * n) :=
  ⟨row.val * n + column.val, by
    calc
      row.val * n + column.val < row.val * n + n := Nat.add_lt_add_left column.isLt _
      _ = (row.val + 1) * n := by rw [Nat.add_mul]; simp
      _ ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt row.isLt)⟩

@[simp] theorem flatIndex_div (row : Fin m) (column : Fin n) :
    (flatIndex row column).val / n = row.val := by
  have hn : 0 < n := Nat.zero_lt_of_lt column.isLt
  simp [flatIndex, Nat.mul_comm row.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt column.isLt]

@[simp] theorem flatIndex_mod (row : Fin m) (column : Fin n) :
    (flatIndex row column).val % n = column.val := by
  simp [flatIndex, Nat.mul_comm row.val n, Nat.mod_eq_of_lt column.isLt]

namespace Expr

/-- Instantiate input ports with expressions and relocate registers. All references
remain bounded and in the same domain; substitution cannot introduce a logic loop. -/
def bind (inputs : Fin i → Expr d j s) (registers : Fin r → Fin s) : Expr d i r → Expr d j s
  | .lit b => .lit b
  | .input k => inputs k
  | .reg k => .reg (registers k)
  | .inv a => .inv (a.bind inputs registers)
  | .and a b => .and (a.bind inputs registers) (b.bind inputs registers)
  | .xor a b => .xor (a.bind inputs registers) (b.bind inputs registers)
  | .mux c a b => .mux (c.bind inputs registers) (a.bind inputs registers) (b.bind inputs registers)

@[simp] theorem eval_bind (e : Expr d i r) (inputs : Fin i → Expr d j s)
    (registers : Fin r → Fin s) (xs state) :
    (e.bind inputs registers).eval xs state =
      e.eval (fun k => (inputs k).eval xs state) (fun k => state (registers k)) := by
  induction e <;> simp_all [bind, eval]

end Expr

namespace Circuit

/-- Module connections either use a top-level input or a bounded instance output.
Every feedback source is Moore, so it reads only pre-edge state. -/
inductive Connection (external instances ports : Nat) where
  | input (index : Fin external)
  | output (instanceIndex : Fin instances) (port : Fin ports)
  deriving Repr, DecidableEq

def unpack (values : Fin (count * bits) → Bool) : Fin count → Fin bits → Bool :=
  fun j k => values (flatIndex j k)

private def portExpr (ms : Fin count → Circuit d i r o) (j : Fin count) (k : Fin o) :
    Expr d external (count * r) :=
  (ms j).output[k].bind (fun _ => .lit false) (flatIndex j)

private def connectionExpr (ms : Fin count → Circuit d i r o)
    (connection : Connection external count o) : Expr d external (count * r) :=
  match connection with
  | .input k => .input k
  | .output j k => portExpr ms j k

private def instanceState (ms : Fin count → Circuit d i r o)
    (wire : Fin count → Fin i → Connection external count o) (j : Fin count) :
    Vector (Register d external (count * r)) r :=
  (ms j).state.map fun reg =>
    ⟨s!"u{j.val}/{reg.name}", reg.reset,
      reg.next.bind (fun k => connectionExpr ms (wire j k)) (flatIndex j), reg.source⟩

/-- Flatten typed Moore instances into the ordinary proved circuit path. The proof
argument makes the feedback restriction explicit at the elaboration boundary. -/
def network (ms : Fin count → Circuit d i r o) (_moore : ∀ j, (ms j).IsMoore)
    (wire : Fin count → Fin i → Connection external count o) :
    Circuit d external (count * r) (count * o) where
  name := "network"
  state := (Vector.ofFn (instanceState ms wire)).flatten
  output := (Vector.ofFn fun j => Vector.ofFn (portExpr ms j)).flatten

def networkInputs (ms : Fin count → Circuit d i r o)
    (wire : Fin count → Fin i → Connection external count o)
    (state : Fin count → Fin r → Bool) (xs : Fin external → Bool) (j : Fin count) : Fin i → Bool :=
  fun k => match wire j k with
    | .input n => xs n
    | .output a b => (ms a).evalOutput (state a) (fun _ => false) b

/-- Independent instance semantics. All next-state functions sample the same old
state and the same reset edge, including in cyclic ready/valid networks. -/
def networkModel (ms : Fin count → Circuit d i r o)
    (wire : Fin count → Fin i → Connection external count o) :
    PMachine (Fin count → Fin r → Bool) ((Fin external → Bool) × Bool) (Fin count → Fin o → Bool) where
  out state j := (ms j).evalOutput (state j) (fun _ => false)
  next state xs j := (ms j).next (state j) (networkInputs ms wire state xs.1 j, xs.2)

@[simp] private theorem portExpr_eval (ms : Fin count → Circuit d i r o)
    (j : Fin count) (k : Fin o) (xs : Fin external → Bool) (state) :
    (portExpr ms j k).eval xs state = (ms j).evalOutput (unpack state j) (fun _ => false) k := by
  simp [portExpr, Expr.eval_bind, Expr.eval, evalOutput]
  rfl

@[simp] private theorem connectionExpr_eval (ms : Fin count → Circuit d i r o)
    (connection : Connection external count o) (xs : Fin external → Bool) (state) :
    (connectionExpr ms connection).eval xs state = match connection with
      | .input k => xs k
      | .output j k => (ms j).evalOutput (unpack state j) (fun _ => false) k := by
  cases connection <;> simp [connectionExpr, Expr.eval]

theorem network_isMoore (ms : Fin count → Circuit d i r o) (hm : ∀ j, (ms j).IsMoore)
    (wire : Fin count → Fin i → Connection external count o) : (network ms hm wire).IsMoore := by
  intro state a b
  funext k
  simp [network, evalOutput, portExpr, Expr.eval_bind, Expr.eval]

/-- Each physical instance transition equals its local semantic transition. -/
theorem network_next (ms : Fin count → Circuit d i r o) (hm : ∀ j, (ms j).IsMoore)
    (wire : Fin count → Fin i → Connection external count o) (state xs) :
    unpack ((network ms hm wire).next state xs) =
      (networkModel ms wire).next (unpack state) xs := by
  funext j k
  simp only [unpack, next, network, networkModel]
  simp [instanceState, Expr.eval_bind]
  rfl

theorem network_output (ms : Fin count → Circuit d i r o) (hm : ∀ j, (ms j).IsMoore)
    (wire : Fin count → Fin i → Connection external count o) (state xs) :
    unpack ((network ms hm wire).evalOutput state xs) = (networkModel ms wire).out (unpack state) := by
  funext j k
  simp [network, evalOutput, unpack]
  rfl

/-- Physical elaboration preserves the complete arbitrary-power-up trace. -/
theorem network_correct (ms : Fin count → Circuit d i r o) (hm : ∀ j, (ms j).IsMoore)
    (wire : Fin count → Fin i → Connection external count o) (state₀ xs t) :
    unpack (((network ms hm wire).denote (network_isMoore ms hm wire)).runFrom state₀ xs t) =
      (networkModel ms wire).runFrom (unpack state₀) xs t := by
  have hs : ∀ t, unpack (((network ms hm wire).denote (network_isMoore ms hm wire)).stateFrom state₀ xs t) =
      (networkModel ms wire).stateFrom (unpack state₀) xs t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [PMachine.stateFrom_succ]
      change unpack ((network ms hm wire).next _ _) = _
      rw [network_next]
      exact congrArg (fun s => (networkModel ms wire).next s (xs t)) ih
  unfold PMachine.runFrom
  change unpack ((network ms hm wire).evalOutput _ _) = _
  rw [network_output]
  exact congrArg (networkModel ms wire).out (hs t)

end Circuit
end HDLean
