import HDLean.Backend.Graph

namespace HDLean.Backend

/-- Input and old-state variables cannot alias even when their numeric indices agree. -/
inductive Variable where
  | input (index : Nat)
  | state (index : Nat)
  deriving Repr, DecidableEq, BEq, Ord

/-- Canonical local Boolean expressions used by the translation checker. -/
inductive Formula where
  | lit (value : Bool)
  | atom (index : Variable)
  | inv (arg : Formula)
  | and (left right : Formula)
  deriving Repr, DecidableEq, BEq

namespace Formula

/-- A total structural order. Lean's derived recursive `Ord` uses opaque native
code, so the checker uses this explicit definition to permit kernel replay. -/
def order : Formula → Formula → Ordering
  | .lit a, .lit b => compare a b
  | .lit _, _ => .lt
  | _, .lit _ => .gt
  | .atom a, .atom b => compare a b
  | .atom _, _ => .lt
  | _, .atom _ => .gt
  | .inv a, .inv b => order a b
  | .inv _, _ => .lt
  | _, .inv _ => .gt
  | .and a b, .and c d => (order a c).then (order b d)

instance : Ord Formula := ⟨order⟩

def eval (v : Variable → Bool) : Formula → Bool
  | .lit b => b
  | .atom k => v k
  | .inv a => !(a.eval v)
  | .and a b => a.eval v && b.eval v

def negate : Formula → Formula
  | .lit b => .lit (!b)
  | .inv a => a
  | a => .inv a

@[simp] theorem eval_negate (a : Formula) (v) : (negate a).eval v = !(a.eval v) := by
  cases a <;> simp [negate, eval]

def conjunction (a b : Formula) : Formula :=
  if a = .lit false ∨ b = .lit false then .lit false
  else if a = .lit true then b
  else if b = .lit true ∨ a = b then a
  else if a = negate b then .lit false
  else if compare a b = .gt then .and b a else .and a b

@[simp] theorem eval_conjunction (a b : Formula) (v) :
    (conjunction a b).eval v = (a.eval v && b.eval v) := by
  unfold conjunction
  split
  · rename_i h
    rcases h with h | h <;> subst_vars <;> simp [eval]
  · split
    · subst_vars; simp [eval]
    · split
      · rename_i h
        rcases h with h | h <;> subst_vars <;> simp [eval]
      · split
        · rename_i h
          rw [h, eval_negate]
          simp [eval]
        · split <;> simp [eval, Bool.and_comm]

def normalize : Formula → Formula
  | .inv a => negate (normalize a)
  | .and a b => conjunction (normalize a) (normalize b)
  | a => a

@[simp] theorem eval_normalize (a : Formula) (v) : (normalize a).eval v = a.eval v := by
  induction a with
  | lit b => rfl
  | atom k => rfl
  | inv a ih => simp [normalize, eval, ih]
  | and a b ha hb => simp [normalize, eval, ha, hb]

end Formula

/-- Decode one AIG literal, preserving its inversion bit. Missing variables are false,
matching the total graph evaluator; graph well-formedness is checked separately. -/
def symbolicLit (values : Array Formula) (l : Lit) : Formula :=
  let a := values[l / 2]?.getD (.lit false)
  if l % 2 == 1 then a.negate else a

@[simp] theorem symbolicLit_correct (values : Array Formula) (l : Lit) (v) :
    (symbolicLit values l).eval v = litValue (values.map (Formula.eval v)) l := by
  simp only [symbolicLit, litValue, Array.getElem?_map]
  rw [show false = Formula.eval v (.lit false) from rfl, Option.getD_map]
  split <;> simp_all [Bool.xor, Formula.eval_negate, Formula.eval]

def symbolicGates (gates : Array Gate) (initial : Array Formula) : Array Formula :=
  gates.foldl (fun values gate => values.push
    (Formula.conjunction (symbolicLit values gate.a) (symbolicLit values gate.b))) initial

/-- A single kernel theorem validates graph reconstruction for every graph and valuation. -/
theorem symbolicGates_correct (gates : Array Gate) (initial : Array Formula) (v) :
    (symbolicGates gates initial).map (Formula.eval v) =
      gates.foldl (fun values gate => values.push
        (litValue values gate.a && litValue values gate.b)) (initial.map (Formula.eval v)) := by
  rw [symbolicGates, ← Array.foldl_toList, ← Array.foldl_toList]
  generalize gates.toList = gs
  induction gs generalizing initial with
  | nil => rfl
  | cons gate gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp

def symbolicInitial (inputs latches : Nat) : Array Formula :=
  #[.lit false] ++ (Array.range inputs).map (fun k => .atom (.input k)) ++
    (Array.range latches).map (fun k => .atom (.state k))

def assignment (inputs state : Array Bool) : Variable → Bool
  | .input k => inputs[k]?.getD false
  | .state k => state[k]?.getD false

theorem symbolicInitial_correct (inputs state : Array Bool) :
    (symbolicInitial inputs.size state.size).map (Formula.eval (assignment inputs state)) =
      #[false] ++ inputs ++ state := by
  simp only [symbolicInitial, Array.map_append, Array.map_map]
  congr 1
  · congr 1
    · simp [Formula.eval]
    · apply Array.ext
      · simp
      · intro k h₁ h₂
        simp [Formula.eval, assignment, Array.getElem?_eq_getElem h₂]
  · apply Array.ext
    · simp
    · intro k h₁ h₂
      simp [Formula.eval, assignment, Array.getElem?_eq_getElem h₂]

def Graph.symbolicValues (g : Graph) : Array Formula :=
  symbolicGates g.gates (symbolicInitial g.inputs g.latches)

theorem Graph.symbolicValues_correct (g : Graph) (inputs state : Array Bool)
    (hi : inputs.size = g.inputs) (hr : state.size = g.latches) :
    g.symbolicValues.map (Formula.eval (assignment inputs state)) = g.values inputs state := by
  rw [Graph.symbolicValues, symbolicGates_correct, ← hi, ← hr, symbolicInitial_correct]
  rfl

def _root_.HDLean.Netlist.Node.symbolic : Netlist.Node d i r → Formula
  | .lit b => .lit b
  | .input k => .atom (.input k.val)
  | .reg k => .atom (.state k.val)
  | .inv a => a.symbolic.negate
  | .and a b => Formula.conjunction a.symbolic b.symbolic

@[simp] theorem node_symbolic_correct (n : Netlist.Node d i r) (v : Variable → Bool) :
    n.symbolic.eval v = n.eval (fun k => v (.input k.val)) (fun k => v (.state k.val)) := by
  induction n with
  | lit b => rfl
  | input k => rfl
  | reg k => rfl
  | inv a ih => simp [Netlist.Node.symbolic, Netlist.Node.eval, ih]
  | and a b ha hb => simp [Netlist.Node.symbolic, Netlist.Node.eval, ha, hb]

def symbolicMux (c a b : Formula) : Formula :=
  Formula.negate (Formula.conjunction
    (Formula.negate (Formula.conjunction c a))
    (Formula.negate (Formula.conjunction (Formula.negate c) b)))

@[simp] theorem symbolicMux_correct (c a b : Formula) (v) :
    (symbolicMux c a b).eval v = if c.eval v then a.eval v else b.eval v := by
  simp only [symbolicMux, Formula.eval_negate, Formula.eval_conjunction]
  cases c.eval v <;> cases a.eval v <;> cases b.eval v <;> rfl

def symbolicNext (c : Circuit d i r o) : Array Formula :=
  (Vector.ofFn fun k : Fin r =>
    let reg := c.state[k]
    match reg.reset with
    | .unreset => (lowerExpr reg.next).symbolic
    | .hold => symbolicMux (.atom (.input i)) (.atom (.state k.val)) (lowerExpr reg.next).symbolic
    | .synchronous b => symbolicMux (.atom (.input i)) (.lit b) (lowerExpr reg.next).symbolic).toArray

def symbolicOutput (c : Circuit d i r o) : Array Formula :=
  c.output.toArray.map fun e => (lowerExpr e).symbolic

def Graph.Validates (g : Graph) (c : Circuit d i r o) : Prop :=
  g.wellFormed = true ∧ g.inputs = i + 1 ∧ g.latches = r ∧ g.outputs.size = o ∧
  g.next.map (symbolicLit g.symbolicValues) = symbolicNext c ∧
  g.outputs.map (symbolicLit g.symbolicValues) = symbolicOutput c

instance (g : Graph) (c : Circuit d i r o) : Decidable (g.Validates c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- An executable translation validator. It accepts only structurally identical normalized
Boolean cones. Its completeness is unnecessary; rejection cannot ship unproved logic. -/
def Graph.validate (g : Graph) (c : Circuit d i r o) : Bool := decide (g.Validates c)

@[simp] theorem assignment_input (xs : Vector Bool i) (state : Vector Bool r)
    (rst : Bool) (k : Fin i) :
    assignment (xs.toArray.push rst) state.toArray (.input k.val) = xs[k] := by
  simp [assignment, Array.getElem?_push, Nat.ne_of_lt k.isLt]

@[simp] theorem assignment_reset (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    assignment (xs.toArray.push rst) state.toArray (.input i) = rst := by
  simp [assignment, Array.getElem_push]

@[simp] theorem assignment_state (xs : Vector Bool i) (state : Vector Bool r)
    (rst : Bool) (k : Fin r) :
    assignment (xs.toArray.push rst) state.toArray (.state k.val) = state[k] := by
  simp [assignment]

@[simp] theorem node_assignment_correct (n : Netlist.Node d i r)
    (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    n.symbolic.eval (assignment (xs.toArray.push rst) state.toArray) =
      n.eval (fun k => xs[k]) (fun k => state[k]) := by
  rw [node_symbolic_correct]
  congr 1 <;> funext k <;> simp

theorem symbolicNext_correct (c : Circuit d i r o)
    (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    (symbolicNext c).map (Formula.eval (assignment (xs.toArray.push rst) state.toArray)) =
      (Vector.ofFn (c.next (fun k => state[k]) ((fun k => xs[k]), rst))).toArray := by
  apply Array.ext
  · simp [symbolicNext]
  · intro k h₁ h₂
    have hk : k < r := by simpa using h₂
    cases h : c.state[k].reset <;>
      simp [symbolicNext, Circuit.next, h, Formula.eval, lowerExpr_correct, assignment_state xs state rst ⟨k,hk⟩]

theorem symbolicOutput_correct (c : Circuit d i r o)
    (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    (symbolicOutput c).map (Formula.eval (assignment (xs.toArray.push rst) state.toArray)) =
      (Vector.ofFn (c.evalOutput (fun k => state[k]) (fun k => xs[k]))).toArray := by
  apply Array.ext
  · simp [symbolicOutput]
  · intro k h₁ h₂
    simp [symbolicOutput, Circuit.evalOutput, lowerExpr_correct]

/-- Accepted graph translations preserve every next-state and output bit, including reset,
for arbitrary power-up values. Neither the compiler nor its cache is trusted. -/
theorem Graph.validate_sound (g : Graph) (c : Circuit d i r o)
    (h : g.validate c = true) : g.Equivalent c := by
  have h' : g.Validates c := of_decide_eq_true h
  obtain ⟨hw, hi, hr, ho, hn, hout⟩ := h'
  refine ⟨hw, hi, hr, ho, ?_⟩
  intro xs state rst
  let v := assignment (xs.toArray.push rst) state.toArray
  have hv := g.symbolicValues_correct (xs.toArray.push rst) state.toArray
    (by simp [hi]) (by simp [hr])
  have hl (l : Lit) : (symbolicLit g.symbolicValues l).eval v =
      litValue (g.values (xs.toArray.push rst) state.toArray) l := by
    rw [symbolicLit_correct, hv]
  apply Prod.ext
  · change g.next.map _ = _
    rw [← symbolicNext_correct c xs state rst, ← hn, Array.map_map]
    exact Array.map_congr_left (fun l _ => (hl l).symm)
  · change g.outputs.map _ = _
    rw [← symbolicOutput_correct c xs state rst, ← hout, Array.map_map]
    exact Array.map_congr_left (fun l _ => (hl l).symm)

/-- Compilation is an untrusted search followed by a proved, fail-closed validator. -/
def checkedCompile (c : Circuit d i r o) : Except String {g : Graph // g.Equivalent c} :=
  let g := compile (lower c)
  if h : g.validate c = true then .ok ⟨g, g.validate_sound c h⟩
  else .error "shared-graph translation validation failed"

end HDLean.Backend
