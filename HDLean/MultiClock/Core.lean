import HDLean.Core.Circuit
import HDLean.Semantics.Clock
import HDLean.Core.WordBank

namespace HDLean.MultiClock

/-!
Legacy multi-clock circuits: a single-domain tree circuit with a clock label per
register. Logic may read any register, and coincident edges always sample the old
value, so this model cannot express metastability. New multi-clock designs use
`MultiClock.Shared.MultiDag`, whose only cross-domain edges are synchronizers and
whose semantics carries the sampling oracle. The dual-clock FIFO hardware still
uses this model until it is migrated (milestone R2).
-/

/-- Each state bit is physically clocked by a bounded, static domain identity.
Edges are semantic events, never synthesized data enables. -/
structure Circuit (nd inputs regs outputs : Nat) where
  combinational : HDLean.Circuit 0 inputs regs outputs
  clock : Fin regs → Fin nd

/-- All right-hand sides see the pre-event state; only clocks with an edge commit. -/
def Circuit.next (c : Circuit nd i r o) (s : Fin r → Bool)
    (xs : (Fin i → Bool) × Bool) (edge : Fin nd → Bool) : Fin r → Bool :=
  fun k => if edge (c.clock k) then c.combinational.next s xs k else s k

def Circuit.output (c : Circuit nd i r o) (s : Fin r → Bool) (xs : Fin i → Bool) : Fin o → Bool :=
  c.combinational.evalOutput s xs

/-- The only direct domain-crossing constructor is explicitly named and typed. -/
structure Synchronizer (source target : Fin nd) (width : Nat) where
  first : BitVec width
  second : BitVec width

def Synchronizer.step (s : Synchronizer source target width)
    (old new : Signal source.val (BitVec width)) (mask : BitVec width)
    (edge reset : Bool) : Synchronizer source target width :=
  if edge then
    if reset then ⟨0, 0⟩ else ⟨sampleBits old.value new.value mask, s.first⟩
  else s

/-- The second flop samples the old first flop on the destination clock. -/
theorem Synchronizer.second_samples_first (s : Synchronizer source target width) (old new mask) :
    (s.step old new mask true false).second = s.first := rfl

/-- Event encoding: each domain edge becomes an ordinary input, so the circuit can
be emitted through the single-clock proved emitter. -/
def Circuit.eventCircuit (c : Circuit nd i r o) : HDLean.Circuit 0 (i+1+nd) r o :=
  let wire : Fin i → Expr 0 (i+1+nd) r := fun k => .input ⟨k.val, by omega⟩
  let rst : Expr 0 (i+1+nd) r := .input ⟨i, by omega⟩
  { name := c.combinational.name ++ "_events"
    state := Vector.ofFn fun k =>
      let reg := c.combinational.state[k]
      let rhs := reg.next.bind wire id
      let candidate := match reg.reset with
        | .unreset => rhs
        | .hold => .mux rst (.reg k) rhs
        | .synchronous b => .mux rst (.lit b) rhs
      ⟨reg.name, .unreset,
        .mux (.input ⟨i+1+(c.clock k).val, by omega⟩) candidate (.reg k), reg.source⟩
    output := c.combinational.output.map (fun e => e.bind wire id) }

def Circuit.eventInputs (xs : Fin i → Bool) (rst : Bool) (edge : Fin nd → Bool) :
    Fin (i+1+nd) → Bool := fun k =>
  if h : k.val < i then xs ⟨k.val,h⟩
  else if he : k.val = i then rst else edge ⟨k.val-i-1, by omega⟩

/-- Explicit edge inputs reproduce exactly the physical event semantics. -/
theorem Circuit.eventCircuit_correct (c : Circuit nd i r o) (s xs rst edge unusedReset) :
    c.eventCircuit.next s (eventInputs xs rst edge, unusedReset) = c.next s (xs,rst) edge ∧
    c.eventCircuit.evalOutput s (eventInputs xs rst edge) = c.output s xs := by
  constructor
  · funext k
    simp only [eventCircuit, HDLean.Circuit.next, Fin.getElem_fin, Vector.getElem_ofFn, Expr.eval,
      ]
    have hwire : (fun k : Fin i => eventInputs xs rst edge ⟨k.val, by omega⟩) = xs := by
      funext k; simp [eventInputs, k.isLt]
    simp only [Circuit.next, HDLean.Circuit.next]
    have hedge : eventInputs xs rst edge ⟨i+1+(c.clock k).val, by omega⟩ = edge (c.clock k) := by
      simp [eventInputs, show ¬ i+1+(c.clock k).val < i by omega,
        show i+1+(c.clock k).val ≠ i by omega]
      congr 1
      apply Fin.ext
      simp
      omega
    have hreset : eventInputs xs rst edge ⟨i, by omega⟩ = rst := by simp [eventInputs]
    simp only [hedge]
    cases (c.combinational.state[k]).reset <;> simp [Expr.eval, Expr.eval_bind, hwire, hreset]
  · funext k
    simp only [eventCircuit, HDLean.Circuit.evalOutput, Circuit.output,
      Fin.getElem_fin, Vector.getElem_map, Expr.eval_bind, Expr.eval, id_eq]
    congr 1
    funext j
    simp [eventInputs, j.isLt]

/-- A named, domain-typed two-flop crossing constructor. The first stage reads
the source signal; the second reads the old first stage in the target domain. -/
def sync2Words {source target : Fin nd}
    (reset : Signal target.val (Expr 0 inputs regs))
    (crossing : Signal source.val (WordExpr 0 inputs regs width))
    (first : Signal target.val (WordExpr 0 inputs regs width)) :
    WordExpr 0 inputs regs width × WordExpr 0 inputs regs width :=
  (WordExpr.mux reset.value (WordExpr.literal 0) crossing.value,
   WordExpr.mux reset.value (WordExpr.literal 0) first.value)

/-- A bank assigns one physical clock to each word, with all bits sharing it. -/
def wordBank (name : String) (clock : Fin count → Fin nd)
    (reset : Fin count → ResetKind)
    (words : Fin count → WordExpr 0 inputs (count*width) width)
    (outputs : Vector (Expr 0 inputs (count*width)) outBits) : Circuit nd inputs (count*width) outBits :=
  ⟨HDLean.wordBank name reset words outputs,
   fun k => ((Vector.ofFn fun j : Fin count => Vector.replicate width (clock j)).flatten)[k]⟩

theorem wordBank_next (name : String) (clock : Fin count → Fin nd) (reset : Fin count → ResetKind)
    (words : Fin count → WordExpr 0 inputs (count*width) width)
    (outputs : Vector (Expr 0 inputs (count*width)) outBits) (s xs rst edge) (j : Fin count) :
    (bankWord j : WordExpr 0 inputs (count*width) width).eval xs
      ((wordBank name clock reset words outputs).next s (xs,rst) edge) =
      if edge (clock j) then
        match reset j with
        | .unreset => (words j).eval xs s
        | .hold => if rst then (bankWord j : WordExpr 0 inputs (count*width) width).eval xs s else (words j).eval xs s
        | .synchronous b => if rst then if b then -1 else 0 else (words j).eval xs s
      else (bankWord j : WordExpr 0 inputs (count*width) width).eval xs s := by
  have hs : (bankWord j : WordExpr 0 inputs (count*width) width).eval xs
      ((wordBank name clock reset words outputs).next s (xs,rst) edge) =
      if edge (clock j) then (bankWord j : WordExpr 0 inputs (count*width) width).eval xs
        ((HDLean.wordBank name reset words outputs).next s (xs,rst))
      else (bankWord j : WordExpr 0 inputs (count*width) width).eval xs s := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [WordExpr.eval_bit _ _ _ k hk]
    simp only [bankWord, Vector.getElem_ofFn, Expr.eval, Circuit.next, wordBank,
      Fin.getElem_fin, Vector.getElem_flatten, Vector.getElem_ofFn, Vector.getElem_replicate,
      flatIndex_div]
    cases he : edge (clock j) with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      simpa only [bankWord, Vector.getElem_ofFn, Expr.eval] using (WordExpr.eval_bit (bankWord j : WordExpr 0 inputs (count*width) width) xs s k hk).symm
    | true =>
      simp only [↓reduceIte]
      simpa only [bankWord, Vector.getElem_ofFn, Expr.eval] using (WordExpr.eval_bit (bankWord j : WordExpr 0 inputs (count*width) width) xs
        ((HDLean.wordBank name reset words outputs).next s (xs,rst)) k hk).symm
  rw [hs, HDLean.wordBank_next]
  rfl

end HDLean.MultiClock
