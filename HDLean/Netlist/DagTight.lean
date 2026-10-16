import HDLean.Netlist.DagLower

/-!
# Gate-count-preserving lowering

`Dag.lowerTight` lowers a node graph to an and-inverter graph with a wire
table instead of a fixed layout: a negation costs no gate (it flips the wire's
polarity), an AND is one gate, a XOR or mux three, and constants, inputs and
registers are wires. Synchronous reset to a constant is one gate per register,
hold three, none for free-running registers.

`lowerTight_correct` and `lowerTight_wellFormed` are the same contract as
`lower_correct` and `lower_wellFormed`, so every proved text backend can use it.
-/
namespace HDLean.Dag
open Backend

set_option linter.unusedSimpArgs false

/-- Node wires and the gates emitted so far (numbered from `i+r+2`). -/
structure Tight where
  wires : Array Wire
  gates : Array Gate

def Tight.wire (t : Tight) (k : Nat) : Wire := t.wires.getD k ⟨0, false⟩

def tightOp (base : Nat) (t : Tight) : Op d i r → Tight
  | .lit b => ⟨t.wires.push ⟨0, b⟩, t.gates⟩
  | .input k => ⟨t.wires.push ⟨k.val + 1, false⟩, t.gates⟩
  | .reg k => ⟨t.wires.push ⟨i + 2 + k.val, false⟩, t.gates⟩
  | .not a => ⟨t.wires.push (t.wire a).flip, t.gates⟩
  | .and a b =>
    ⟨t.wires.push ⟨base + t.gates.size, false⟩, t.gates.push ⟨base + t.gates.size, (t.wire a).encode, (t.wire b).encode⟩⟩
  | .xor a b =>
    ⟨t.wires.push ⟨base + t.gates.size + 2, true⟩,
      t.gates ++ (muxGates (base + t.gates.size) (t.wire a) (t.wire b).flip (t.wire b)).toArray⟩
  | .mux c a b =>
    ⟨t.wires.push ⟨base + t.gates.size + 2, true⟩,
      t.gates ++ (muxGates (base + t.gates.size) (t.wire c) (t.wire a) (t.wire b)).toArray⟩

def tightNodes (base : Nat) (ops : List (Op d i r)) (t : Tight) : Tight := ops.foldl (tightOp base) t

/-- The next-state wire of one register and its gates, appended at index `n`. -/
def resetGates (i : Nat) (n : Nat) (reg : Wire) (next : Wire) : ResetKind → Wire × List Gate
  | .unreset => (next, [])
  | .hold => (⟨n + 2, true⟩, muxGates n ⟨i + 1, false⟩ reg next)
  | .synchronous false => (⟨n, false⟩, [⟨n, (Wire.mk (i + 1) true).encode, next.encode⟩])
  | .synchronous true => (⟨n, true⟩, [⟨n, (Wire.mk (i + 1) true).encode, next.flip.encode⟩])

/-- Reset logic for registers `k, k+1, ...`. -/
def resetAll (i : Nat) (nodeWire : Nat → Wire) : Nat → List (Nat × ResetKind) → Nat → List Wire × List Gate
  | _, [], _ => ([], [])
  | n, (nx, kind) :: rest, k =>
    let p := resetGates i n ⟨i + 2 + k, false⟩ (nodeWire nx) kind
    let q := resetAll i nodeWire (n + p.2.length) rest (k + 1)
    (p.1 :: q.1, p.2 ++ q.2)

def regList (c : Dag d i r o) : List (Nat × ResetKind) := (List.finRange r).map fun k => (c.next[k], c.reset[k])

def lowerTight (c : Dag d i r o) : Graph :=
  let t := tightNodes (i + r + 2) c.nodes ⟨#[], #[]⟩
  let rs := resetAll i t.wire (i + r + 2 + t.gates.size) (regList c) 0
  { name := c.name
    inputs := i + 1
    latches := r
    gates := t.gates ++ rs.2.toArray
    next := (rs.1.map Wire.encode).toArray
    outputs := c.out.toArray.map fun k => (t.wire k).encode
    inputNames := c.inputNames.toArray.push "rst"
    stateNames := c.stateNames.toArray
    outputNames := c.outputNames.toArray
    sources := c.sources.toArray }

/-! ## Correctness -/

/-- The gates so far, evaluated on the initial values, give every node's value
through its wire. -/
structure TightRel (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) (source : Array Bool) (t : Tight) :
    Prop where
  size : t.wires.size = source.size
  bound : ∀ k, k < source.size → (t.wire k).index < i + r + 2 + t.gates.size
  value : ∀ k, k < source.size → (t.wire k).value (run t.gates.toList (initial xs state rst)) = read source k
  wf : GatesWF (i + r + 2) t.gates.toList

theorem tightRel_initial (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    TightRel xs state rst #[] ⟨#[], #[]⟩ :=
  ⟨rfl, fun _ h => by simp at h, fun _ h => by simp at h, trivial⟩

theorem run_initial_size (gs : List Gate) (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    (run gs (initial xs state rst)).size = i + r + 2 + gs.length := by simp

theorem initial_ext (gs : List Gate) (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    Extends (initial xs state rst) (run gs (initial xs state rst)) := run_extends _ _

theorem wire_const (gs : List Gate) (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) (b : Bool) :
    (Wire.mk 0 b).value (run gs (initial xs state rst)) = b := by
  simp only [Wire.value]
  rw [(initial_ext gs xs state rst).2 0 (by simp), initial_zero]; simp

theorem wire_input (gs : List Gate) (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) (k : Fin i) :
    (Wire.mk (k.val + 1) false).value (run gs (initial xs state rst)) = xs[k] := by
  simp only [Wire.value, Bool.xor_false]
  rw [(initial_ext gs xs state rst).2 _ (by simp; omega), initial_input]

theorem wire_reset (gs : List Gate) (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    (Wire.mk (i + 1) false).value (run gs (initial xs state rst)) = rst := by
  simp only [Wire.value, Bool.xor_false]
  rw [(initial_ext gs xs state rst).2 _ (by simp; omega), initial_reset]

theorem wire_reg (gs : List Gate) (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) (k : Fin r) :
    (Wire.mk (i + 2 + k.val) false).value (run gs (initial xs state rst)) = state[k] := by
  simp only [Wire.value, Bool.xor_false]
  rw [(initial_ext gs xs state rst).2 _ (by simp; omega), initial_state]

theorem Tight.wire_push (t : Tight) (w : Wire) (k : Nat) (hk : k < t.wires.size) :
    (⟨t.wires.push w, g⟩ : Tight).wire k = t.wire k := by
  simp [Tight.wire, Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt hk]

theorem Tight.wire_push_self (t : Tight) (w : Wire) : (⟨t.wires.push w, g⟩ : Tight).wire t.wires.size = w := by
  simp [Tight.wire, Array.getD_eq_getD_getElem?]

theorem run_push_gate (gs : List Gate) (g : Gate) (v : Array Bool) :
    run (gs ++ [g]) v = (run gs v).push (litValue (run gs v) g.a && litValue (run gs v) g.b) := by
  simp [run, List.foldl_append]

theorem TightRel.step (hr : TightRel (i := i) (r := r) xs state rst source t) (op : Op d i r)
    (h : op.Valid source.size) :
    TightRel xs state rst (source.push (op.eval (fun k => xs[k]) (fun k => state[k]) (read source)))
      (tightOp (i + r + 2) t op) := by
  have hsz := run_initial_size t.gates.toList xs state rst
  simp only [Array.length_toList] at hsz
  -- old wires keep their values when gates are appended
  have keep : ∀ (more : List Gate) (k : Nat), k < source.size →
      (t.wire k).value (run (t.gates.toList ++ more) (initial xs state rst)) = read source k := by
    intro more k hk
    rw [run_append, Wire.value_extends (run_extends _ _) _ (by rw [hsz]; exact hr.bound k hk)]
    exact hr.value k hk
  have pushRead : ∀ (x : Bool) (k : Nat), k < source.size → read (source.push x) k = read source k := by
    intro x k hk; simp [read, Array.getElem?_push, Nat.ne_of_lt hk]
  have pushSelf : ∀ x : Bool, read (source.push x) source.size = x := by intro x; simp [read]
  -- the generic shape: one new wire `w`, gates `more`
  have generic : ∀ (w : Wire) (more : List Gate),
      GatesWF (i + r + 2 + t.gates.size) more →
      w.index < i + r + 2 + t.gates.size + more.length →
      w.value (run (t.gates.toList ++ more) (initial xs state rst)) =
        op.eval (fun k => xs[k]) (fun k => state[k]) (read source) →
      TightRel xs state rst (source.push (op.eval (fun k => xs[k]) (fun k => state[k]) (read source)))
        ⟨t.wires.push w, t.gates ++ more.toArray⟩ := by
    intro w more hm hw hv
    refine ⟨by simp [hr.size], fun k hk => ?_, fun k hk => ?_, ?_⟩
    rotate_right
    · simp only [Array.toList_append, List.toList_toArray, gatesWF_append, Array.length_toList]
      exact ⟨hr.wf, hm⟩
    · simp only [Array.size_push] at hk
      simp only [Array.size_append, List.size_toArray]
      by_cases old : k < source.size
      · rw [Tight.wire_push _ _ _ (by rw [hr.size]; exact old)]
        have := hr.bound k old; omega
      · have : k = source.size := by omega
        subst this
        rw [← hr.size, Tight.wire_push_self]; omega
    · simp only [Array.size_push] at hk
      simp only [Array.toList_append, List.toList_toArray]
      by_cases old : k < source.size
      · rw [Tight.wire_push _ _ _ (by rw [hr.size]; exact old), keep more k old, pushRead _ _ old]
      · have : k = source.size := by omega
        subst this
        rw [← hr.size, Tight.wire_push_self, hv, hr.size, pushSelf]
  have wa : ∀ a, a < source.size → (t.wire a).index < i + r + 2 + t.gates.size := hr.bound
  have va : ∀ a, a < source.size → (t.wire a).value (run t.gates.toList (initial xs state rst)) = read source a :=
    hr.value
  cases op with
  | lit b =>
    have := generic ⟨0, b⟩ [] trivial (by simp; omega) (by simp [wire_const, Op.eval])
    simpa [tightOp] using this
  | input k =>
    have := generic ⟨k.val + 1, false⟩ [] trivial (by simp; omega) (by simp [wire_input, Op.eval])
    simpa [tightOp] using this
  | reg k =>
    have := generic ⟨i + 2 + k.val, false⟩ [] trivial (by simp; omega) (by simp [wire_reg, Op.eval])
    simpa [tightOp] using this
  | not a =>
    simp only [Op.Valid] at h
    have := generic (t.wire a).flip [] trivial (by simp [Wire.flip]; exact wa a h)
      (by simp only [List.append_nil, Wire.value_flip, va a h, Op.eval])
    simpa [tightOp] using this
  | and a b =>
    simp only [Op.Valid] at h
    have := generic ⟨i + r + 2 + t.gates.size, false⟩ [⟨i + r + 2 + t.gates.size, (t.wire a).encode, (t.wire b).encode⟩]
      ⟨rfl, by rw [Wire.encode_div]; exact wa a h.1, by rw [Wire.encode_div]; exact wa b h.2, trivial⟩ (by simp) (by
        rw [run_push_gate]
        simp only [Wire.value, read, Array.getElem?_push, hsz, ↓reduceIte, Option.getD_some, Bool.xor_false]
        rw [Wire.litValue, Wire.litValue, va a h.1, va b h.2]; rfl)
    have e : t.gates.push ⟨i + r + 2 + t.gates.size, (t.wire a).encode, (t.wire b).encode⟩ =
        t.gates ++ [⟨i + r + 2 + t.gates.size, (t.wire a).encode, (t.wire b).encode⟩].toArray := by simp
    simp only [tightOp]; rw [e]; exact this
  | xor a b =>
    simp only [Op.Valid] at h
    have hm := mux_value (run t.gates.toList (initial xs state rst)) (t.wire a) (t.wire b).flip (t.wire b)
      (by rw [hsz]; exact wa a h.1) (by rw [hsz]; simp only [Wire.flip]; exact wa b h.2) (by rw [hsz]; exact wa b h.2)
    have := generic ⟨i + r + 2 + t.gates.size + 2, true⟩
      (muxGates (i + r + 2 + t.gates.size) (t.wire a) (t.wire b).flip (t.wire b))
      (muxGates_wf _ _ _ _ (wa a h.1) (by simp only [Wire.flip]; exact wa b h.2) (wa b h.2)) (by simp [muxGates]) (by
        rw [run_append, ← hsz, hm]
        simp only [Wire.value_flip, va a h.1, va b h.2, Op.eval]
        cases read source a <;> cases read source b <;> rfl)
    simpa [tightOp] using this
  | mux c a b =>
    simp only [Op.Valid] at h
    have hm := mux_value (run t.gates.toList (initial xs state rst)) (t.wire c) (t.wire a) (t.wire b)
      (by rw [hsz]; exact wa c h.1) (by rw [hsz]; exact wa a h.2.1) (by rw [hsz]; exact wa b h.2.2)
    have := generic ⟨i + r + 2 + t.gates.size + 2, true⟩
      (muxGates (i + r + 2 + t.gates.size) (t.wire c) (t.wire a) (t.wire b))
      (muxGates_wf _ _ _ _ (wa c h.1) (wa a h.2.1) (wa b h.2.2)) (by simp [muxGates]) (by
        rw [run_append, ← hsz, hm]
        simp only [va c h.1, va a h.2.1, va b h.2.2, Op.eval])
    simpa [tightOp] using this

theorem tightNodes_correct (ops : List (Op d i r))
    (hr : TightRel (i := i) (r := r) xs state rst source t) (h : NodesWF source.size ops) :
    TightRel xs state rst (evalNodes ops (fun k => xs[k]) (fun k => state[k]) source)
      (tightNodes (i + r + 2) ops t) := by
  induction ops generalizing source t with
  | nil => exact hr
  | cons op ops ih =>
    have hs := hr.step op h.1
    have hh : NodesWF (source.push (op.eval (fun k => xs[k]) (fun k => state[k]) (read source))).size ops := by
      simpa using h.2
    simpa only [evalNodes, List.foldl_cons, tightNodes] using ih hs hh

/-! ## Reset logic -/

theorem resetGates_spec (n : Nat) (v : Array Bool) (hv : v.size = n) (reg next : Wire) (kind : ResetKind)
    (hreg : reg.index < n) (hnext : next.index < n) (hrst : i + 1 < n) :
    GatesWF n (resetGates i n reg next kind).2 ∧
    (resetGates i n reg next kind).1.index < n + (resetGates i n reg next kind).2.length ∧
    (resetGates i n reg next kind).1.value (run (resetGates i n reg next kind).2 v) =
      resetValue kind (reg.value v) (next.value v) ((Wire.mk (i + 1) false).value v) := by
  cases kind with
  | unreset => exact ⟨trivial, by simp [resetGates]; omega, by simp [resetGates, run, resetValue]⟩
  | hold =>
    have hm := mux_value v ⟨i + 1, false⟩ reg next (by rw [hv]; exact hrst) (by rw [hv]; exact hreg)
      (by rw [hv]; exact hnext)
    rw [hv] at hm
    refine ⟨muxGates_wf _ _ _ _ hrst hreg hnext, by simp [resetGates, muxGates], ?_⟩
    simp only [resetGates]
    rw [hm]; rfl
  | synchronous b =>
    cases b with
    | false =>
      refine ⟨⟨rfl, by simp [Wire.encode_div]; omega, by rw [Wire.encode_div]; exact hnext, trivial⟩,
        by simp [resetGates], ?_⟩
      simp only [resetGates, run, List.foldl_cons, List.foldl_nil, Wire.litValue, Wire.value_flip]
      simp only [Wire.value, read, Array.getElem?_push, hv, ↓reduceIte, Option.getD_some, Bool.xor_false,
        Bool.xor_true, resetValue]
      cases v[i + 1]?.getD false <;> simp
    | true =>
      refine ⟨⟨rfl, by simp [Wire.encode_div]; omega, by simp [Wire.flip, Wire.encode_div]; exact hnext, trivial⟩,
        by simp [resetGates], ?_⟩
      simp only [resetGates, run, List.foldl_cons, List.foldl_nil, Wire.litValue, Wire.value_flip]
      simp only [Wire.value, read, Array.getElem?_push, hv, ↓reduceIte, Option.getD_some, Bool.xor_false,
        Bool.xor_true, resetValue]
      cases v[i + 1]?.getD false <;> simp

theorem resetAll_spec (nw : Nat → Wire) (v0 : Array Bool) (hbase : i + r + 2 ≤ v0.size) :
    ∀ (rs : List (Nat × ResetKind)) (k : Nat) (pre : List Gate),
      (∀ p ∈ rs, (nw p.1).index < v0.size) → k + rs.length ≤ r →
      GatesWF (v0.size + pre.length) (resetAll i nw (v0.size + pre.length) rs k).2 ∧
      (resetAll i nw (v0.size + pre.length) rs k).1.length = rs.length ∧
      ∀ j (hj : j < rs.length),
        ((resetAll i nw (v0.size + pre.length) rs k).1.getD j ⟨0, false⟩).index <
          v0.size + pre.length + (resetAll i nw (v0.size + pre.length) rs k).2.length ∧
        ((resetAll i nw (v0.size + pre.length) rs k).1.getD j ⟨0, false⟩).value
          (run (pre ++ (resetAll i nw (v0.size + pre.length) rs k).2) v0) =
          resetValue rs[j].2 ((Wire.mk (i + 2 + (k + j)) false).value v0) ((nw rs[j].1).value v0)
            ((Wire.mk (i + 1) false).value v0)
  | [], _, _, _, _ => ⟨trivial, rfl, fun j hj => by simp at hj⟩
  | (nx, kind) :: rest, k, pre, hn, hk => by
    simp only [List.length_cons] at hk
    have hnx : (nw nx).index < v0.size := hn (nx, kind) (by simp)
    have hsz : (run pre v0).size = v0.size + pre.length := by simp
    have hext : Extends v0 (run pre v0) := run_extends _ _
    have keep : ∀ w : Wire, w.index < v0.size → w.value (run pre v0) = w.value v0 :=
      fun w hw => Wire.value_extends hext w hw
    obtain ⟨p1, p2, p3⟩ := resetGates_spec (i := i) (v0.size + pre.length) (run pre v0) hsz ⟨i + 2 + k, false⟩ (nw nx)
      kind (by simp; omega) (by omega) (by omega)
    generalize hp : resetGates i (v0.size + pre.length) ⟨i + 2 + k, false⟩ (nw nx) kind = p at p1 p2 p3
    have ih := resetAll_spec nw v0 hbase rest (k + 1) (pre ++ p.2) (fun q hq => hn q (by simp [hq]))
      (by omega)
    simp only [List.length_append, ← Nat.add_assoc] at ih
    obtain ⟨q1, q2, q3⟩ := ih
    simp only [resetAll, hp]
    refine ⟨?_, by simp [q2], fun j hj => ?_⟩
    · rw [gatesWF_append]; exact ⟨p1, q1⟩
    · cases j with
      | zero =>
        simp only [List.getD_cons_zero, List.length_append, List.getElem_cons_zero]
        refine ⟨by omega, ?_⟩
        rw [← List.append_assoc, run_append (pre ++ p.2), Wire.value_extends (run_extends _ _) _
          (by simp; omega), run_append, p3, keep _ (by simp; omega), keep _ hnx, keep _ (by simp; omega)]
        simp
      | succ j =>
        have hj' : j < rest.length := by simpa using hj
        obtain ⟨b1, b2⟩ := q3 j hj'
        simp only [List.getD_cons_succ, List.length_append, List.getElem_cons_succ]
        refine ⟨by omega, ?_⟩
        rw [← List.append_assoc, b2]
        simp [Nat.add_assoc, Nat.add_comm 1 j]

/-! ## The lowered graph -/

theorem getD_get {α : Type} (l : List α) (d : α) (j : Nat) (h : j < l.length) : l.getD j d = l[j] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem resetAll_length (nw : Nat → Wire) : ∀ (n : Nat) (rs : List (Nat × ResetKind)) (k : Nat),
    (resetAll i nw n rs k).1.length = rs.length
  | _, [], _ => rfl
  | n, p :: rest, k => by simp [resetAll, resetAll_length]

theorem regList_length (c : Dag d i r o) : (regList c).length = r := by simp [regList]

theorem regList_get (c : Dag d i r o) (j : Nat) (hj : j < (regList c).length) :
    (regList c)[j] = (c.next[j]'(by simpa [regList_length] using hj), c.reset[j]'(by simpa [regList_length] using hj)) := by
  simp [regList]

theorem regList_bound (c : Dag d i r o) : ∀ p ∈ regList c, p.1 < c.nodes.length := by
  intro p hp
  simp only [regList, List.mem_map, List.mem_finRange, true_and] at hp
  obtain ⟨k, rfl⟩ := hp
  exact c.wf.2.1 k

theorem tight_rel (c : Dag d i r o) (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    TightRel xs state rst (c.values (fun k => xs[k]) (fun k => state[k])) (tightNodes (i + r + 2) c.nodes ⟨#[], #[]⟩) :=
  tightNodes_correct c.nodes (tightRel_initial xs state rst) (by simpa using c.wf.1)

theorem lowerTight_values (c : Dag d i r o) (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    (lowerTight c).values (xs.toArray.push rst) state.toArray =
      run ((tightNodes (i + r + 2) c.nodes ⟨#[], #[]⟩).gates.toList ++
        (resetAll i (tightNodes (i + r + 2) c.nodes ⟨#[], #[]⟩).wire
          (i + r + 2 + (tightNodes (i + r + 2) c.nodes ⟨#[], #[]⟩).gates.size) (regList c) 0).2)
        (initial xs state rst) := by
  simp [lowerTight, Graph.values, ← Array.foldl_toList, initial, run, List.foldl_append]

theorem lowerTight_correct (c : Dag d i r o) (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool) :
    (lowerTight c).eval (xs.toArray.push rst) state.toArray =
      ((Vector.ofFn (c.nextState (fun k => state[k]) ((fun k => xs[k]), rst))).toArray,
       (Vector.ofFn (c.evalOutput (fun k => state[k]) (fun k => xs[k]))).toArray) := by
  have hr := tight_rel c xs state rst
  generalize ht : tightNodes (i + r + 2) c.nodes ⟨#[], #[]⟩ = t at hr
  have hs : (c.values (fun k => xs[k]) (fun k => state[k])).size = c.nodes.length := values_size c _ _
  let v0 := run t.gates.toList (initial xs state rst)
  have hv0 : v0.size = i + r + 2 + t.gates.size := by simp [v0]
  have spec := resetAll_spec (i := i) (r := r) t.wire v0 (by rw [hv0]; omega) (regList c) 0 []
    (fun p hp => by rw [hv0]; exact hr.bound _ (by rw [hs]; exact regList_bound c p hp)) (by simp [regList_length])
  simp only [List.length_nil, Nat.add_zero, List.nil_append] at spec
  rw [hv0] at spec
  obtain ⟨-, slen, sval⟩ := spec
  have hvals := lowerTight_values c xs state rst
  rw [ht] at hvals
  apply Prod.ext
  · apply Array.ext
    · simp [Graph.eval, lowerTight, ht, slen, regList_length]
    · intro k h1 h2
      have hk : k < r := by simpa [Graph.eval, lowerTight, ht, slen, regList_length] using h1
      have hk' : k < (regList c).length := by rw [regList_length]; exact hk
      obtain ⟨-, hval⟩ := sval k hk'
      simp only [Graph.eval, Array.getElem_map, Vector.getElem_toArray, Vector.getElem_ofFn]
      simp only [hvals]
      simp only [lowerTight, ht, List.getElem_toArray, List.getElem_map]
      rw [run_append, Wire.litValue, ← getD_get _ ⟨0, false⟩, hval]
      simp only [regList_get, Nat.zero_add, nextState, v0]
      rw [wire_reg _ xs state rst ⟨k, hk⟩, wire_reset, hr.value _ (by rw [hs]; exact c.wf.2.1 ⟨k, hk⟩)]
      rfl
  · apply Array.ext
    · simp [Graph.eval, lowerTight]
    · intro k h1 h2
      have hk : k < o := by simpa [Graph.eval, lowerTight] using h1
      have hb : c.out[k] < c.nodes.length := c.wf.2.2 ⟨k, hk⟩
      simp only [Graph.eval, Array.getElem_map, Vector.getElem_toArray, Vector.getElem_ofFn]
      simp only [hvals]
      simp only [lowerTight, ht, Array.getElem_map, Vector.getElem_toArray]
      rw [Wire.litValue, run_append, Wire.value_extends (run_extends _ _) _
        (by simp; exact hr.bound _ (by rw [hs]; exact hb)), hr.value _ (by rw [hs]; exact hb)]
      rfl

theorem lowerTight_wellFormed (c : Dag d i r o) : (lowerTight c).wellFormed = true := by
  have hr := tight_rel c (Vector.replicate i false) (Vector.replicate r false) false
  generalize ht : tightNodes (i + r + 2) c.nodes ⟨#[], #[]⟩ = t at hr
  have hs := values_size c (fun k => (Vector.replicate i false)[k]) (fun k => (Vector.replicate r false)[k])
  let v0 := run t.gates.toList (initial (Vector.replicate i false) (Vector.replicate r false) false)
  have hv0 : v0.size = i + r + 2 + t.gates.size := by simp [v0]
  have spec := resetAll_spec (i := i) (r := r) t.wire v0 (by rw [hv0]; omega) (regList c) 0 []
    (fun p hp => by rw [hv0]; exact hr.bound _ (by rw [hs]; exact regList_bound c p hp)) (by simp [regList_length])
  simp only [List.length_nil, Nat.add_zero, List.nil_append] at spec
  rw [hv0] at spec
  obtain ⟨swf, slen, sval⟩ := spec
  apply graph_wellFormed
  · simp [lowerTight]
  · simp [lowerTight, ht, slen, regList_length]
  · simp [lowerTight]
  · simp [lowerTight]
  · simp [lowerTight]
  · simp [lowerTight]
  · simp only [lowerTight, ht, Array.toList_append, List.toList_toArray]
    have heq : i + 1 + r + 1 = i + r + 2 := by omega
    rw [heq, gatesWF_append]
    exact ⟨hr.wf, by simpa using swf⟩
  · intro l hl
    simp only [lowerTight, ht, List.toList_toArray, List.mem_map] at hl
    obtain ⟨w, hw, rfl⟩ := hl
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    have hj' : j < (regList c).length := by rw [← slen]; exact hj
    have := (sval j hj').1
    rw [getD_get _ _ _ hj] at this
    simp only [lowerTight, ht, Wire.encode_div, Array.size_append, List.size_toArray]
    exact Nat.lt_of_lt_of_eq this (by omega)
  · intro l hl
    simp only [lowerTight, ht, Array.toList_map, List.mem_map] at hl
    obtain ⟨n, hn, rfl⟩ := hl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hn
    have hk' : k < o := by simpa using hk
    have hb : c.out[k] < c.nodes.length := c.wf.2.2 ⟨k, hk'⟩
    have := hr.bound _ (by rw [hs]; simpa using hb)
    simp only [lowerTight, ht, Wire.encode_div, Array.size_append, List.size_toArray]
    have e : c.out.toArray.toList[k] = c.out[k] := by simp
    rw [e]
    exact Nat.lt_of_lt_of_le this (by omega)

@[simp] theorem lowerTight_next_size (c : Dag d i r o) : (lowerTight c).next.size = (lowerTight c).latches := by
  simp [lowerTight, resetAll_length, regList_length]

end HDLean.Dag
