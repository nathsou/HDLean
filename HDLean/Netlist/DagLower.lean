import HDLean.Core.Dag
import HDLean.Backend.Graph

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace HDLean.Dag
open Backend

/-- Internal AIG wire; polarity is explicit so numbering needs no table or cache. -/
structure Wire where
  index : Nat
  negative : Bool
  deriving Repr

def Wire.encode (w : Wire) : Lit := 2*w.index + if w.negative then 1 else 0
def Wire.flip (w : Wire) : Wire := ⟨w.index, !w.negative⟩
def Wire.value (w : Wire) (values : Array Bool) : Bool := xor (read values w.index) w.negative

@[simp] theorem Wire.encode_div (w : Wire) : w.encode / 2 = w.index := by
  rcases w with ⟨n,b⟩; cases b <;> simp [Wire.encode, Nat.add_div]

@[simp] theorem Wire.litValue (w : Wire) (values : Array Bool) :
    litValue values w.encode = w.value values := by
  rcases w with ⟨n,b⟩; cases b <;> simp [Wire.encode, Backend.litValue, Wire.value, read, Nat.add_div]

@[simp] theorem Wire.value_flip (w : Wire) (values) : w.flip.value values = !(w.value values) := by
  simp only [Wire.flip, Wire.value]
  cases read values w.index <;> cases w.negative <;> rfl

/-- Exactly three AND gates implement one mux; its output is the inverted last gate. -/
def muxGates (start : Nat) (sel yes no : Wire) : List Gate :=
  [⟨start, sel.encode, yes.encode⟩,
   ⟨start+1, sel.flip.encode, no.encode⟩,
   ⟨start+2, (Wire.mk start true).encode, (Wire.mk (start+1) true).encode⟩]

def nodeWire (base k : Nat) : Wire := ⟨base+3*k+2,true⟩
def nodeLit (base k : Nat) : Lit := (nodeWire base k).encode

def opWires (base : Nat) : Op d i r → Wire × Wire × Wire
  | .lit b => (⟨0,true⟩, ⟨0,b⟩, ⟨0,b⟩)
  | .input k => (⟨0,true⟩, ⟨k.val+1,false⟩, ⟨k.val+1,false⟩)
  | .reg k => (⟨0,true⟩, ⟨i+2+k.val,false⟩, ⟨i+2+k.val,false⟩)
  | .not a => (nodeWire base a, ⟨0,false⟩, ⟨0,true⟩)
  | .and a b => (nodeWire base a, nodeWire base b, ⟨0,false⟩)
  | .xor a b => (nodeWire base a, (nodeWire base b).flip, nodeWire base b)
  | .mux c a b => (nodeWire base c, nodeWire base a, nodeWire base b)

/-- Constant-size list concatenation: logical reduction preserves every explicit share. -/
def lowerNodes (base : Nat) : Nat → List (Op d i r) → List Gate
  | _, [] => []
  | k, op::rest =>
    let (s,a,b) := opWires base op
    muxGates (base+3*k) s a b ++ lowerNodes base (k+1) rest

def resetWires (inputs base index : Nat) (next : Nat) (kind : ResetKind) : Wire × Wire × Wire :=
  let n := nodeWire base next
  match kind with
  | .unreset => (⟨0,true⟩, n, n)
  | .hold => (⟨inputs+1,false⟩, ⟨inputs+2+index,false⟩, n)
  | .synchronous b => (⟨inputs+1,false⟩, ⟨0,b⟩, n)

/-- One list fold is used only for semantics, never to discover sharing during lowering. -/
def run (gs : List Gate) (v : Array Bool) : Array Bool :=
  gs.foldl (fun v g => v.push (litValue v g.a && litValue v g.b)) v

@[simp] theorem run_append (a b : List Gate) (v) : run (a++b) v = run b (run a v) := by
  simp [run, List.foldl_append]

@[simp] theorem run_size (gs : List Gate) (a : Array Bool) :
    (run gs a).size = a.size + gs.length := by
  induction gs generalizing a with
  | nil => simp [run]
  | cons g gs ih => simp only [run, List.foldl_cons] at *; rw [ih]; simp; omega

def Extends (a b : Array Bool) : Prop :=
  a.size ≤ b.size ∧ ∀ j, j < a.size → read b j = read a j

theorem extends_refl (a : Array Bool) : Extends a a := ⟨Nat.le_refl _, fun _ _ => rfl⟩
theorem extends_push (a : Array Bool) (b : Bool) : Extends a (a.push b) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  simp [read, Array.getElem?_push, Nat.ne_of_lt hj]
theorem extends_trans {a b c : Array Bool} (h : Extends a b) (k : Extends b c) : Extends a c :=
  ⟨Nat.le_trans h.1 k.1, fun j hj => (k.2 j (Nat.lt_of_lt_of_le hj h.1)).trans (h.2 j hj)⟩
theorem run_extends (gs : List Gate) (a : Array Bool) : Extends a (run gs a) := by
  induction gs generalizing a with
  | nil => exact extends_refl _
  | cons g gs ih => exact extends_trans (extends_push _ _) (ih _)

theorem Wire.value_extends {a b : Array Bool} (h : Extends a b) (w : Wire) (hw : w.index < a.size) :
    w.value b = w.value a := by simp only [Wire.value, h.2 _ hw]

@[simp] theorem lowerNodes_length (base k : Nat) (ops : List (Op d i r)) :
    (lowerNodes base k ops).length = 3*ops.length := by
  induction ops generalizing k with
  | nil => rfl
  | cons op ops ih => simp [lowerNodes, muxGates, ih]; omega

theorem run_mux (v : Array Bool) (sel yes no : Wire)
    (hs : sel.index < v.size) (ha : yes.index < v.size) (hb : no.index < v.size) :
    run (muxGates v.size sel yes no) v =
      ((v.push (sel.value v && yes.value v)).push (!sel.value v && no.value v)).push
        (!(sel.value v && yes.value v) && !(!sel.value v && no.value v)) := by
  simp only [run, muxGates, List.foldl_cons, List.foldl_nil, Wire.litValue, Wire.value_flip]
  simp only [Wire.value, read, Array.getElem?_push, Array.size_push,
    Nat.ne_of_lt hs, Nat.ne_of_lt ha, Nat.ne_of_lt hb,
    show v.size ≠ v.size+1 by omega, show v.size+1 ≠ v.size by omega,
    ↓reduceIte, Option.getD_some, Bool.xor_true, Bool.xor_false]


theorem mux_value (v : Array Bool) (sel yes no : Wire)
    (hs : sel.index < v.size) (ha : yes.index < v.size) (hb : no.index < v.size) :
    (Wire.mk (v.size+2) true).value (run (muxGates v.size sel yes no) v) =
      if sel.value v then yes.value v else no.value v := by
  rw [run_mux v sel yes no hs ha hb]
  simp only [Wire.value, read, Array.getElem?_push, Array.size_push,
    ↓reduceIte, Option.getD_some, Bool.xor_true]
  have hm (c a b : Bool) : (!(!(c && a) && !(!c && b))) = (if c then a else b) := by
    cases c <;> cases a <;> cases b <;> rfl
  exact hm _ _ _

def initial (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) : Array Bool :=
  #[false] ++ xs.toArray.push rst ++ state.toArray

@[simp] theorem initial_size (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    (initial xs state rst).size = i+r+2 := by simp [initial]; omega

@[simp] theorem initial_zero (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    read (initial xs state rst) 0 = false := by simp [initial, read, Array.getElem?_append]

@[simp] theorem initial_input (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) (k : Fin i) :
    read (initial xs state rst) (k.val+1) = xs[k] := by
  simp [initial, read, Array.getElem?_append, Array.getElem?_push, k.isLt,
    show k.val < i+1 by omega, show k.val ≠ i by omega, show k.val+1 < 1+(i+1) by omega, Array.getElem_push]

@[simp] theorem initial_reset (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    read (initial xs state rst) (i+1) = rst := by
  simp [initial, read, Array.getElem?_append, Array.getElem?_push, Array.getElem_push]

@[simp] theorem initial_state (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) (k : Fin r) :
    read (initial xs state rst) (i+2+k.val) = state[k] := by
  simp [initial, read, Array.getElem?_append, show ¬ i+2+k.val < 1+(i+1) by omega,
    show i+2+k.val-(1+(i+1)) = k.val by omega]

structure Related (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool)
    (source target : Array Bool) : Prop where
  size : target.size = i+r+2+3*source.size
  initialExt : Extends (initial xs state rst) target
  nodes : ∀ k, k < source.size → (nodeWire (i+r+2) k).value target = read source k

theorem related_initial (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    Related xs state rst #[] (initial xs state rst) :=
  ⟨by simp, extends_refl _, fun _ h => by simp at h⟩

theorem Related.zero (h : Related xs state rst source target) : read target 0 = false := by
  rw [h.initialExt.2 0 (by simp), initial_zero]

theorem Related.input (h : Related (i := i) xs state rst source target) (k : Fin i) :
    (Wire.mk (k.val+1) false).value target = xs[k] := by
  simp only [Wire.value, Bool.xor_false]
  rw [h.initialExt.2 _ (by simp; omega), initial_input]

theorem Related.regValue (h : Related (i := i) (r := r) xs state rst source target) (k : Fin r) :
    (Wire.mk (i+2+k.val) false).value target = state[k] := by
  simp only [Wire.value, Bool.xor_false]
  rw [h.initialExt.2 _ (by simp; omega), initial_state]

theorem Related.reset (h : Related (i := i) xs state rst source target) :
    (Wire.mk (i+1) false).value target = rst := by
  simp only [Wire.value, Bool.xor_false]
  rw [h.initialExt.2 _ (by simp; omega), initial_reset]

theorem Related.constant (h : Related xs state rst source target) (b : Bool) :
    (Wire.mk 0 b).value target = b := by simp [Wire.value, h.zero]

theorem opWires_bounded (op : Op d i r) (h : op.Valid k) :
    let w := opWires (i+r+2) op
    w.1.index < i+r+2+3*k ∧ w.2.1.index < i+r+2+3*k ∧ w.2.2.index < i+r+2+3*k := by
  cases op <;> simp [opWires, Op.Valid, nodeWire, Wire.flip] at * <;> omega

theorem opWires_correct (op : Op d i r) (h : op.Valid source.size)
    (hr : Related (i := i) (r := r) xs state rst source target) :
    let w := opWires (i+r+2) op
    (if w.1.value target then w.2.1.value target else w.2.2.value target) =
      op.eval (fun k => xs[k]) (fun k => state[k]) (read source) := by
  cases op with
  | lit b => simp [opWires, Op.eval, hr.constant]
  | input k => simp [opWires, Op.eval, hr.constant, hr.input]
  | reg k => simp [opWires, Op.eval, hr.constant, hr.regValue]
  | not a =>
    simp only [Op.Valid] at h
    simp only [opWires, Op.eval, hr.nodes a h, hr.constant]
    cases read source a <;> rfl
  | and a b =>
    simp only [Op.Valid] at h
    simp only [opWires, Op.eval, hr.nodes a h.1, hr.nodes b h.2, hr.constant]
    cases read source a <;> cases read source b <;> rfl
  | xor a b =>
    simp only [Op.Valid] at h
    simp only [opWires, Op.eval, hr.nodes a h.1, Wire.value_flip, hr.nodes b h.2]
    cases read source a <;> cases read source b <;> rfl
  | mux c a b =>
    simp only [Op.Valid] at h
    simp only [opWires, Op.eval, hr.nodes c h.1, hr.nodes a h.2.1, hr.nodes b h.2.2]

theorem Related.step (hr : Related (i := i) (r := r) xs state rst source target)
    (op : Op d i r) (h : op.Valid source.size) :
    Related xs state rst (source.push (op.eval (fun k => xs[k]) (fun k => state[k]) (read source)))
      (run (muxGates (i+r+2+3*source.size) (opWires (i+r+2) op).1
        (opWires (i+r+2) op).2.1 (opWires (i+r+2) op).2.2) target) := by
  have hb := opWires_bounded op h
  rw [← hr.size] at hb ⊢
  refine ⟨?_, extends_trans hr.initialExt (run_extends _ _), ?_⟩
  · simp [run_size, muxGates, hr.size]; omega
  · intro k hk
    simp only [Array.size_push] at hk
    by_cases old : k < source.size
    · rw [Wire.value_extends (run_extends _ _) _ (by simp [nodeWire, hr.size]; omega), hr.nodes k old]
      simp [read, Array.getElem?_push, Nat.ne_of_lt old]
    · have heq : k = source.size := by omega
      subst k
      have hw : nodeWire (i+r+2) source.size = Wire.mk (target.size+2) true := by
        simp [nodeWire, hr.size]
      rw [hw, mux_value _ _ _ _ hb.1 hb.2.1 hb.2.2, opWires_correct op h hr]
      simp [read, Array.getElem?_push]

theorem lowerNodes_correct (ops : List (Op d i r))
    (hr : Related (i := i) (r := r) xs state rst source target)
    (h : NodesWF source.size ops) :
    Related xs state rst
      (evalNodes ops (fun k => xs[k]) (fun k => state[k]) source)
      (run (lowerNodes (i+r+2) source.size ops) target) := by
  induction ops generalizing source target with
  | nil => exact hr
  | cons op ops ih =>
    have hs := hr.step op h.1
    have hh : NodesWF (source.push (op.eval (fun k => xs[k]) (fun k => state[k]) (read source))).size ops := by
      simpa using h.2
    have result := ih hs hh
    simpa only [evalNodes, List.foldl_cons, lowerNodes, run_append, Array.size_push] using result

def lowerMuxes (start : Nat) : List (Wire × Wire × Wire) → List Gate
  | [] => []
  | (s,a,b)::rest => muxGates start s a b ++ lowerMuxes (start+3) rest

@[simp] theorem lowerMuxes_length (start : Nat) (ws : List (Wire × Wire × Wire)) :
    (lowerMuxes start ws).length = 3*ws.length := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih => rcases w with ⟨s,a,b⟩; simp [lowerMuxes, muxGates, ih]; omega

def WiresBounded (n : Nat) (w : Wire × Wire × Wire) : Prop :=
  w.1.index < n ∧ w.2.1.index < n ∧ w.2.2.index < n

def muxMeaning (v : Array Bool) (w : Wire × Wire × Wire) : Bool :=
  if w.1.value v then w.2.1.value v else w.2.2.value v

theorem muxMeaning_extends (h : Extends a b) (w) (hw : WiresBounded a.size w) :
    muxMeaning b w = muxMeaning a w := by
  simp only [muxMeaning, Wire.value_extends h _ hw.1,
    Wire.value_extends h _ hw.2.1, Wire.value_extends h _ hw.2.2]

theorem lowerMuxes_correct (ws : List (Wire × Wire × Wire)) (v : Array Bool)
    (hb : ∀ w ∈ ws, WiresBounded v.size w) (k : Nat) (hk : k < ws.length) :
    (Wire.mk (v.size+3*k+2) true).value (run (lowerMuxes v.size ws) v) =
      muxMeaning v ws[k] := by
  induction ws generalizing v k with
  | nil => simp at hk
  | cons w ws ih =>
    rcases w with ⟨s,a,b⟩
    have hw := hb (s,a,b) (by simp)
    have htail : ∀ w ∈ ws, WiresBounded (run (muxGates v.size s a b) v).size w := by
      intro w hm
      have hh := hb w (by simp [hm])
      simp only [run_size, muxGates, List.length_cons, List.length_nil] at ⊢
      unfold WiresBounded at *; omega
    simp only [lowerMuxes, run_append]
    cases k with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
      rw [Wire.value_extends (run_extends _ _) _ (by simp [run_size, muxGates])]
      exact mux_value v s a b hw.1 hw.2.1 hw.2.2
    | succ k =>
      have hk' : k < ws.length := by simpa using hk
      have hh := ih (run (muxGates v.size s a b) v) htail k (by simpa using hk)
      have hsize : (run (muxGates v.size s a b) v).size = v.size+3 := by simp [muxGates]
      rw [hsize] at hh
      have heq : v.size+3*(k+1)+2 = v.size+3+3*k+2 := by omega
      rw [heq, hh]
      exact muxMeaning_extends (run_extends _ _) _ (hb ws[k] (by simp [List.getElem_mem]))

def resetTriples (c : Dag d i r o) : Vector (Wire × Wire × Wire) r :=
  Vector.ofFn fun k => resetWires i (i+r+2) k.val c.next[k] c.reset[k]

/-- A single arithmetic pass, preserving the numbered source graph without search. -/
def lower (c : Dag d i r o) : Graph where
  name := c.name
  inputs := i+1
  latches := r
  gates := (lowerNodes (i+r+2) 0 c.nodes ++
    lowerMuxes (i+r+2+3*c.nodes.length) c.resetTriples.toList).toArray
  next := (Vector.ofFn fun k : Fin r => nodeLit (i+r+2) (c.nodes.length+k.val)).toArray
  outputs := c.out.toArray.map (nodeLit (i+r+2))
  inputNames := c.inputNames.toArray.push "rst"
  stateNames := c.stateNames.toArray
  outputNames := c.outputNames.toArray
  sources := c.sources.toArray

theorem lower_next (c : Dag d i r o) : c.lower.next =
    (Vector.ofFn fun k : Fin r => nodeLit (i+r+2) (c.nodes.length+k.val)).toArray := rfl
theorem lower_outputs (c : Dag d i r o) : c.lower.outputs = c.out.toArray.map (nodeLit (i+r+2)) := rfl

@[simp] theorem lower_inputs (c : Dag d i r o) : c.lower.inputs = i+1 := rfl
@[simp] theorem lower_latches (c : Dag d i r o) : c.lower.latches = r := rfl
@[simp] theorem lower_outputs_size (c : Dag d i r o) : c.lower.outputs.size = o := by simp [lower]
@[simp] theorem lower_gate_count (c : Dag d i r o) : c.lower.gates.size = 3*(c.nodes.length+r) := by
  simp [lower]; omega

theorem resetTriples_bounded (c : Dag d i r o) (k : Fin r) :
    WiresBounded (i+r+2+3*c.nodes.length) c.resetTriples[k] := by
  have hn : c.next[k.val] < c.nodes.length := c.wf.2.1 k
  simp only [resetTriples, Vector.getElem_ofFn]
  cases hk : c.reset[k.val] <;> simp [resetWires, hk, WiresBounded, nodeWire] <;> omega

theorem resetTriples_correct (c : Dag d i r o)
    (hr : Related (i := i) (r := r) xs state rst source target)
    (hs : source.size = c.nodes.length) (k : Fin r) :
    muxMeaning target c.resetTriples[k] =
      resetValue c.reset[k] state[k] (read source c.next[k]) rst := by
  have hn : c.next[k.val] < source.size := by rw [hs]; exact c.wf.2.1 k
  simp only [resetTriples, Vector.getElem_ofFn, muxMeaning]
  cases hk : c.reset[k.val] <;>
    simp [resetWires, hk, resetValue, hr.constant, hr.reset, hr.regValue, hr.nodes _ hn]

theorem lower_values (c : Dag d i r o) (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    c.lower.values (xs.toArray.push rst) state.toArray =
      run (lowerMuxes (i+r+2+3*c.nodes.length) c.resetTriples.toList)
        (run (lowerNodes (i+r+2) 0 c.nodes) (initial xs state rst)) := by
  simp [lower, Graph.values, ← Array.foldl_toList, initial, run, List.foldl_append]

theorem lower_correct (c : Dag d i r o) (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    c.lower.eval (xs.toArray.push rst) state.toArray =
      ((Vector.ofFn (c.nextState (fun k => state[k]) ((fun k => xs[k]), rst))).toArray,
       (Vector.ofFn (c.evalOutput (fun k => state[k]) (fun k => xs[k]))).toArray) := by
  let src := c.values (fun k => xs[k]) (fun k => state[k])
  let mid := run (lowerNodes (i+r+2) 0 c.nodes) (initial xs state rst)
  have hr : Related xs state rst src mid := lowerNodes_correct c.nodes (related_initial xs state rst) c.wf.1
  have hs : src.size = c.nodes.length := values_size c _ _
  have hm : mid.size = i+r+2+3*c.nodes.length := hr.size.trans (by rw [hs])
  have hb : ∀ w ∈ c.resetTriples.toList, WiresBounded mid.size w := by
    intro w hw
    obtain ⟨k,hk,he⟩ := List.getElem_of_mem hw
    subst w
    rw [hm]
    exact c.resetTriples_bounded ⟨k, by simpa using hk⟩
  apply Prod.ext
  · apply Array.ext
    · simp [Graph.eval, lower]
    · intro k h₁ h₂
      have hk : k < r := by simpa [Graph.eval, lower] using h₁
      have result := lowerMuxes_correct c.resetTriples.toList mid hb k (by simpa using hk)
      rw [hm] at result
      have arith : i+r+2+3*(c.nodes.length+k)+2 = i+r+2+3*c.nodes.length+3*k+2 := by omega
      simp only [Graph.eval, lower_next, lower_outputs, Array.getElem_map, Vector.getElem_toArray, Vector.getElem_ofFn]
      change litValue (c.lower.values (xs.toArray.push rst) state.toArray)
        (nodeLit (i+r+2) (c.nodes.length+k)) = _
      rw [lower_values, show nodeLit (i+r+2) (c.nodes.length+k) = (nodeWire (i+r+2) (c.nodes.length+k)).encode from rfl, Wire.litValue]
      change (nodeWire (i+r+2) (c.nodes.length+k)).value _ = _
      simp only [nodeWire, arith]
      rw [result]
      exact c.resetTriples_correct hr hs ⟨k,hk⟩
  · apply Array.ext
    · simp [Graph.eval, lower]
    · intro k h₁ h₂
      have hk : k < o := by simpa [Graph.eval, lower] using h₁
      simp only [Graph.eval, lower_next, lower_outputs, Array.getElem_map, Vector.getElem_toArray, Vector.getElem_ofFn]
      change litValue (c.lower.values (xs.toArray.push rst) state.toArray)
        (nodeLit (i+r+2) c.out[k]) = _
      rw [lower_values, show nodeLit (i+r+2) c.out[k] = (nodeWire (i+r+2) c.out[k]).encode from rfl, Wire.litValue]
      rw [Wire.value_extends (run_extends _ mid) _ (by
        have ho : c.out[k] < c.nodes.length := c.wf.2.2 ⟨k,hk⟩
        simp only [nodeWire, hm]; omega)]
      exact hr.nodes _ (by rw [hs]; exact c.wf.2.2 ⟨k,hk⟩)

/-- Numbering and backwards references of the emitted gate list. -/
def GatesWF : Nat → List Gate → Prop
  | _, [] => True
  | n, g::gs => g.lhs = n ∧ g.a/2 < n ∧ g.b/2 < n ∧ GatesWF (n+1) gs

theorem gatesWF_append (a b : List Gate) (n : Nat) :
    GatesWF n (a++b) ↔ GatesWF n a ∧ GatesWF (n+a.length) b := by
  induction a generalizing n with
  | nil => simp [GatesWF]
  | cons a as ih =>
    simp only [List.cons_append, GatesWF, ih, List.length_cons]
    have heq : n+1+as.length = n+(as.length+1) := by omega
    rw [heq]
    simp only [and_assoc]

theorem muxGates_wf (n : Nat) (s a b : Wire) (hs : s.index < n)
    (ha : a.index < n) (hb : b.index < n) : GatesWF n (muxGates n s a b) := by
  simp only [muxGates, GatesWF, Wire.encode_div, Wire.flip]
  simp only [hs, ha, hb, true_and, and_true]
  exact ⟨Nat.lt_succ_of_lt hs, Nat.lt_succ_of_lt hb, by change n < n+1+1; omega, by change n+1 < n+1+1; omega⟩

theorem lowerNodes_wf (ops : List (Op d i r)) (k : Nat) (h : NodesWF k ops) :
    GatesWF (i+r+2+3*k) (lowerNodes (i+r+2) k ops) := by
  induction ops generalizing k with
  | nil => trivial
  | cons op ops ih =>
    have hb := opWires_bounded op h.1
    simp only [lowerNodes, gatesWF_append]
    refine ⟨muxGates_wf _ _ _ _ hb.1 hb.2.1 hb.2.2, ?_⟩
    have heq : i+r+2+3*k+(muxGates (i+r+2+3*k) (opWires (i+r+2) op).1
        (opWires (i+r+2) op).2.1 (opWires (i+r+2) op).2.2).length = i+r+2+3*(k+1) := by
      simp [muxGates]; omega
    rw [heq]
    exact ih (k+1) h.2

theorem lowerMuxes_wf (ws : List (Wire × Wire × Wire)) (n : Nat)
    (hb : ∀ w ∈ ws, WiresBounded n w) : GatesWF n (lowerMuxes n ws) := by
  induction ws generalizing n with
  | nil => trivial
  | cons w ws ih =>
    rcases w with ⟨s,a,b⟩
    have hw := hb (s,a,b) (by simp)
    simp only [lowerMuxes, gatesWF_append]
    refine ⟨muxGates_wf _ _ _ _ hw.1 hw.2.1 hw.2.2, ?_⟩
    simp only [muxGates, List.length_cons, List.length_nil]
    apply ih
    intro w hm
    have hh := hb w (by simp [hm])
    unfold WiresBounded at *; omega

def wfStep (gate : Gate) (s : Option Bool × Nat) : Id (ForInStep (Option Bool × Nat)) :=
  if gate.lhs != s.2 || gate.a/2 ≥ s.2 || gate.b/2 ≥ s.2 then
    pure (.done (some false,s.2)) else pure (.yield (none,s.2+1))

theorem gatesWF_loop (gs : List Gate) (n : Nat) (h : GatesWF n gs) :
    forIn gs (none,n) wfStep = (pure (none,n+gs.length) : Id (Option Bool × Nat)) := by
  induction gs generalizing n with
  | nil => simp
  | cons g gs ih =>
    have ha : ¬ g.a/2 ≥ n := Nat.not_le_of_gt h.2.1
    have hb : ¬ g.b/2 ≥ n := Nat.not_le_of_gt h.2.2.1
    simp only [List.forIn_cons, wfStep, h.1, bne_self_eq_false, beq_self_eq_true, Bool.not_true, ha, hb,
      decide_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, pure_bind]
    change forIn gs (none,n+1) wfStep = _
    rw [ih (n+1) h.2.2.2]
    have heq : n+1+gs.length = n+(gs.length+1) := by omega
    simp only [List.length_cons, heq]

theorem graph_wellFormed (g : Graph)
    (hi : g.inputs ≠ 0) (hn : g.next.size = g.latches)
    (hin : g.inputNames.size = g.inputs) (hs : g.stateNames.size = g.latches)
    (hsrc : g.sources.size = g.latches) (hout : g.outputNames.size = g.outputs.size)
    (hg : GatesWF (g.inputs+g.latches+1) g.gates.toList)
    (hnext : ∀ l ∈ g.next.toList, l/2 < g.inputs+g.latches+1+g.gates.size)
    (houtput : ∀ l ∈ g.outputs.toList, l/2 < g.inputs+g.latches+1+g.gates.size) :
    g.wellFormed = true := by
  unfold Graph.wellFormed
  simp only [hi, hn, hin, hs, hsrc, hout, bne_self_eq_false, beq_iff_eq,
    Bool.false_or, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  have loop := gatesWF_loop _ _ hg
  unfold wfStep at loop
  rw [loop]
  simp only [pure_bind, Array.length_toList]
  simp [List.all_eq_true, hnext, houtput]

/-- The fixed layout is well formed for every well-formed source DAG. -/
theorem lower_wellFormed (c : Dag d i r o) : c.lower.wellFormed = true := by
  apply graph_wellFormed
  · simp [lower]
  · simp [lower]
  · simp [lower]
  · simp [lower]
  · simp [lower]
  · simp [lower]
  · simp only [lower, List.toList_toArray]
    have heq : i+1+r+1 = i+r+2 := by omega
    rw [heq, gatesWF_append]
    refine ⟨by simpa using lowerNodes_wf c.nodes 0 c.wf.1, ?_⟩
    rw [lowerNodes_length]
    apply lowerMuxes_wf
    intro w hw
    obtain ⟨k,hk,he⟩ := List.getElem_of_mem hw
    subst w
    exact c.resetTriples_bounded ⟨k, by simpa using hk⟩
  · intro l hl
    have hg := lower_gate_count c
    simp only [lower_next, Vector.toList_toArray] at hl
    obtain ⟨k,hk,he⟩ := List.getElem_of_mem hl
    subst l
    simp only [Vector.getElem_toList, Vector.getElem_ofFn, nodeLit, Wire.encode_div,
      nodeWire, lower_inputs, lower_latches, hg]
    have hk' : k < r := by simpa using hk
    change i+r+2+3*(c.nodes.length+k)+2 < i+1+r+1+3*(c.nodes.length+r)
    omega
  · intro l hl
    simp only [lower_outputs, Array.toList_map] at hl
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hl
    obtain ⟨k,hk,he⟩ := List.getElem_of_mem hn
    subst n
    have hk' : k < o := by simpa using hk
    have hb : c.out[k] < c.nodes.length := c.wf.2.2 ⟨k,hk'⟩
    simp only [nodeLit, Wire.encode_div, nodeWire, lower_inputs, lower_latches, lower_gate_count,
      Array.getElem_toList, Vector.getElem_toArray]
    change i+r+2+3*c.out[k]+2 < i+1+r+1+3*(c.nodes.length+r)
    omega

end HDLean.Dag
