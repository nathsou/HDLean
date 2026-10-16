import Designs.AsyncFifo.QueueRefinement

set_option backward.isDefEq.respectTransparency false
namespace HDLean.AsyncFifo

/-- Proof-only absolute counters; the implementation remains the finite physical state. -/
structure Witness {k w : Nat} (s : State k w) where
  ghost : Ghost
  safe : ghost.Safe (2^k)
  controls : ghost.Controls s

variable {k w : Nat} {s : State k w}

private theorem advance_safe_for (v : Witness s) (i : Input k w) (sw sr : Bool) :
    (v.ghost.advance i.writeEdge i.readEdge (push s i) (pop s i) sw sr).Safe (2^k) := by
  apply Ghost.advance_safe v.safe
  · intro hp
    have he : i.writeEdge = true := by simp only [push,Bool.and_eq_true] at hp; exact hp.1.1.1
    exact ⟨he,push_has_space v.safe v.controls hp⟩
  · intro hp
    have he : i.readEdge = true := by simp only [pop,Bool.and_eq_true] at hp; exact hp.1.1.1
    exact ⟨he,pop_has_data v.safe v.controls hp⟩

noncomputable def Witness.step (v : Witness s) (i : Input k w)
    (hwr : i.writeReset = false) (hrr : i.readReset = false) : Witness (next s i) :=
  let h := next_controls v.controls hwr hrr
  let sw := Classical.choose h
  let sr := Classical.choose (Classical.choose_spec h)
  ⟨v.ghost.advance i.writeEdge i.readEdge (push s i) (pop s i) sw sr,
    advance_safe_for v i sw sr,Classical.choose_spec (Classical.choose_spec h)⟩

theorem Witness.step_shape (v : Witness s) (i : Input k w) (hwr hrr) :
    ∃ sw sr, (v.step i hwr hrr).ghost =
      v.ghost.advance i.writeEdge i.readEdge (push s i) (pop s i) sw sr := by
  exact ⟨_,_,rfl⟩

noncomputable def witnesses (v : Witness s) (xs : Nat → Input k w)
    (hreset : ∀ t, (xs t).writeReset = false ∧ (xs t).readReset = false) :
    (t : Nat) → Witness (stateFrom s xs t)
  | 0 => v
  | t+1 => (witnesses v xs hreset t).step (xs t) (hreset t).1 (hreset t).2

/-- Count destination edges, not elapsed source cycles. -/
def edgeCount (edge : Nat → Bool) : Nat → Nat
  | 0 => 0
  | t+1 => edgeCount edge t + if edge t then 1 else 0

theorem edgeCount_mono (edge : Nat → Bool) {a b : Nat} (hab : a ≤ b) :
    edgeCount edge a ≤ edgeCount edge b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases ha : a ≤ b
    · have h := ih ha
      simp only [edgeCount]
      split <;> omega
    · have ha' : a = b+1 := by omega
      subst a
      exact Nat.le_refl _

/-- A bounded-fair schedule supplies three destination edges within three fairness windows. -/
theorem fair_three_edges (hf : QueueSpec.EdgeFair gap edge) :
    ∃ u, u < 3*gap ∧ edge u = true ∧ 2 ≤ edgeCount edge u := by
  obtain ⟨a,ha0,ha,hea⟩ := hf.2 0
  obtain ⟨b,hab,hb,heb⟩ := hf.2 (a+1)
  obtain ⟨u,hbu,hu,heu⟩ := hf.2 (b+1)
  have hca : 1 ≤ edgeCount edge (a+1) := by simp [edgeCount,hea]
  have hcab := edgeCount_mono edge hab
  have hcb : 2 ≤ edgeCount edge (b+1) := by simp [edgeCount,heb]; omega
  have hcbu := edgeCount_mono edge hbu
  exact ⟨u,by omega,heu,by omega⟩

private theorem snapshot_advance (base g : Ghost) (nw nr : Nat)
    (h : base.read ≤ g.read ∧ base.written ≤ g.written ∧
      (1 ≤ nw → base.read ≤ g.readFirst) ∧ (2 ≤ nw → base.read ≤ g.readSecond) ∧
      (1 ≤ nr → base.written ≤ g.writeFirst) ∧ (2 ≤ nr → base.written ≤ g.writeSecond))
    (we re enq deq sw sr : Bool) :
    let g' := g.advance we re enq deq sw sr
    base.read ≤ g'.read ∧ base.written ≤ g'.written ∧
    (1 ≤ nw+(if we then 1 else 0) → base.read ≤ g'.readFirst) ∧
    (2 ≤ nw+(if we then 1 else 0) → base.read ≤ g'.readSecond) ∧
    (1 ≤ nr+(if re then 1 else 0) → base.written ≤ g'.writeFirst) ∧
    (2 ≤ nr+(if re then 1 else 0) → base.written ≤ g'.writeSecond) := by
  cases we <;> cases re <;> cases sw <;> cases sr <;>
    simp_all [Ghost.advance] <;> (repeat' apply And.intro) <;> intros <;> omega

/-- Absolute snapshots never precede the initial committed positions after two receiving edges. -/
theorem witness_snapshot_progress (v : Witness s) (xs : Nat → Input k w)
    (hr : ∀ t, (xs t).writeReset = false ∧ (xs t).readReset = false) (t : Nat) :
    let g := (witnesses v xs hr t).ghost
    v.ghost.read ≤ g.read ∧ v.ghost.written ≤ g.written ∧
    (1 ≤ edgeCount (fun n => (xs n).writeEdge) t → v.ghost.read ≤ g.readFirst) ∧
    (2 ≤ edgeCount (fun n => (xs n).writeEdge) t → v.ghost.read ≤ g.readSecond) ∧
    (1 ≤ edgeCount (fun n => (xs n).readEdge) t → v.ghost.written ≤ g.writeFirst) ∧
    (2 ≤ edgeCount (fun n => (xs n).readEdge) t → v.ghost.written ≤ g.writeSecond) := by
  induction t with
  | zero => simp [witnesses,edgeCount]
  | succ t ih =>
    obtain ⟨sw,sr,heq⟩ := Witness.step_shape (witnesses v xs hr t) (xs t) (hr t).1 (hr t).2
    change (let g := ((witnesses v xs hr t).step (xs t) (hr t).1 (hr t).2).ghost
            v.ghost.read ≤ g.read ∧ v.ghost.written ≤ g.written ∧
            (1 ≤ edgeCount (fun n => (xs n).writeEdge) (t+1) → v.ghost.read ≤ g.readFirst) ∧
            (2 ≤ edgeCount (fun n => (xs n).writeEdge) (t+1) → v.ghost.read ≤ g.readSecond) ∧
            (1 ≤ edgeCount (fun n => (xs n).readEdge) (t+1) → v.ghost.written ≤ g.writeFirst) ∧
            (2 ≤ edgeCount (fun n => (xs n).readEdge) (t+1) → v.ghost.written ≤ g.writeSecond))
    rw [heq]
    dsimp only
    simp only [edgeCount]
    exact snapshot_advance v.ghost (witnesses v xs hr t).ghost _ _ ih _ _ _ _ sw sr

private theorem mod_injective_window {a b d : Nat} (hab : a ≤ b) (hbd : b < a+d)
    (he : a%d = b%d) : a=b := by
  have ha := Nat.mod_add_div a d
  have hb := Nat.mod_add_div b d
  by_cases hq : a/d=b/d
  · rw [hq,he] at ha
    omega
  have hl : a/d ≤ b/d := Nat.div_le_div_right hab
  have hm := Nat.mul_le_mul_left d (show a/d+1 ≤ b/d by omega)
  rw [Nat.mul_add,Nat.mul_one] at hm
  omega

/-- Exact readiness follows from a conservative absolute snapshot with available space. -/
theorem Witness.ready_of_space (v : Witness s)
    (hspace : v.ghost.written < v.ghost.readSecond+2^k) : enqReady s = true := by
  simp only [enqReady,v.controls.1,v.controls.2.2.2.2.2,ungray_gray,bne_iff_ne]
  rw [← add_wrap_bit,← BitVec.ofNat_add]
  intro he
  have hm := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat] at hm
  have hs := v.safe
  unfold Ghost.Safe at hs
  have hpos := Nat.two_pow_pos k
  have hpow : 2^(k+1) = 2*2^k := by rw [Nat.pow_succ,Nat.mul_comm]
  have heq := mod_injective_window (Nat.le_of_lt hspace)
    (show v.ghost.readSecond+2^k < v.ghost.written+2^(k+1) by rw [hpow]; omega) hm
  omega

/-- A synchronized committed position beyond the read head guarantees valid data. -/
theorem Witness.valid_of_data (v : Witness s)
    (hdata : v.ghost.read < v.ghost.writeSecond) : deqValid s = true := by
  simp only [deqValid,v.controls.2.1,v.controls.2.2.2.1,ungray_gray,bne_iff_ne]
  intro he
  have hm := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat] at hm
  have hs := v.safe
  unfold Ghost.Safe at hs
  have hpos := Nat.two_pow_pos k
  have hpow : 2^(k+1) = 2*2^k := by rw [Nat.pow_succ,Nat.mul_comm]
  have heq := mod_injective_window (Nat.le_of_lt hdata)
    (show v.ghost.writeSecond < v.ghost.read+2^(k+1) by rw [hpow]; omega) hm
  omega

theorem witness_written_constant (v : Witness s) (xs : Nat → Input k w)
    (hr : ∀ t, (xs t).writeReset = false ∧ (xs t).readReset = false) (t : Nat)
    (hn : ∀ u, u < t → push (stateFrom s xs u) (xs u) = false) :
    (witnesses v xs hr t).ghost.written = v.ghost.written := by
  induction t with
  | zero => rfl
  | succ t ih =>
    obtain ⟨sw,sr,heq⟩ := Witness.step_shape (witnesses v xs hr t) (xs t) (hr t).1 (hr t).2
    change ((witnesses v xs hr t).step (xs t) (hr t).1 (hr t).2).ghost.written = _
    rw [heq]
    simp only [Ghost.advance,hn t (by omega),Bool.false_eq_true,↓reduceIte,Nat.add_zero]
    exact ih (fun u hu => hn u (by omega))

theorem witness_read_constant (v : Witness s) (xs : Nat → Input k w)
    (hr : ∀ t, (xs t).writeReset = false ∧ (xs t).readReset = false) (t : Nat)
    (hn : ∀ u, u < t → pop (stateFrom s xs u) (xs u) = false) :
    (witnesses v xs hr t).ghost.read = v.ghost.read := by
  induction t with
  | zero => rfl
  | succ t ih =>
    obtain ⟨sw,sr,heq⟩ := Witness.step_shape (witnesses v xs hr t) (xs t) (hr t).1 (hr t).2
    change ((witnesses v xs hr t).step (xs t) (hr t).1 (hr t).2).ghost.read = _
    rw [heq]
    simp only [Ghost.advance,hn t (by omega),Bool.false_eq_true,↓reduceIte,Nat.add_zero]
    exact ih (fun u hu => hn u (by omega))

/-- An offered write with one free slot completes within three fair write-clock windows.
Reads, unrelated edges and every metastable sampling mask remain unconstrained. -/
theorem write_progress (v : Witness s) (xs : Nat → Input k w)
    (hr : ∀ t, (xs t).writeReset = false ∧ (xs t).readReset = false)
    (hf : QueueSpec.EdgeFair gap (fun t => (xs t).writeEdge))
    (hcredit : v.ghost.written-v.ghost.read < 2^k)
    (hoffer : ∀ t, t < 3*gap → (xs t).valid = true) :
    ∃ u, u < 3*gap ∧ push (stateFrom s xs u) (xs u) = true := by
  classical
  by_cases hex : ∃ u, u < 3*gap ∧ push (stateFrom s xs u) (xs u) = true
  · exact hex
  have hn : ∀ u, u < 3*gap → push (stateFrom s xs u) (xs u) = false := by
    intro u hu
    cases he : push (stateFrom s xs u) (xs u) with
    | false => rfl
    | true => exact False.elim (hex ⟨u,hu,he⟩)
  obtain ⟨u,hu,he,hcount⟩ := fair_three_edges hf
  let current := witnesses v xs hr u
  have hwritten := witness_written_constant v xs hr u (fun t ht => hn t (by omega))
  have hsnap := (witness_snapshot_progress v xs hr u).2.2.2.1 hcount
  have hready : enqReady (stateFrom s xs u) = true := by
    apply current.ready_of_space
    change (witnesses v xs hr u).ghost.written < (witnesses v xs hr u).ghost.readSecond+2^k
    rw [hwritten]
    have hbase := v.ghost.occupancy_bound v.safe
    omega
  exact ⟨u,hu,by simp [push,he,(hr u).1,hoffer u hu,hready]⟩

/-- A pending word with a continuously ready reader completes within three fair read-clock windows.
Writes and all sampling choices remain arbitrary. -/
theorem read_progress (v : Witness s) (xs : Nat → Input k w)
    (hr : ∀ t, (xs t).writeReset = false ∧ (xs t).readReset = false)
    (hf : QueueSpec.EdgeFair gap (fun t => (xs t).readEdge))
    (hdata : v.ghost.read < v.ghost.written)
    (hoffer : ∀ t, t < 3*gap → (xs t).ready = true) :
    ∃ u, u < 3*gap ∧ pop (stateFrom s xs u) (xs u) = true := by
  classical
  by_cases hex : ∃ u, u < 3*gap ∧ pop (stateFrom s xs u) (xs u) = true
  · exact hex
  have hn : ∀ u, u < 3*gap → pop (stateFrom s xs u) (xs u) = false := by
    intro u hu
    cases he : pop (stateFrom s xs u) (xs u) with
    | false => rfl
    | true => exact False.elim (hex ⟨u,hu,he⟩)
  obtain ⟨u,hu,he,hcount⟩ := fair_three_edges hf
  let current := witnesses v xs hr u
  have hread := witness_read_constant v xs hr u (fun t ht => hn t (by omega))
  have hsnap := (witness_snapshot_progress v xs hr u).2.2.2.2.2 hcount
  have hvalid : deqValid (stateFrom s xs u) = true := by
    apply current.valid_of_data
    change (witnesses v xs hr u).ghost.read < (witnesses v xs hr u).ghost.writeSecond
    rw [hread]
    omega
  exact ⟨u,hu,by simp [pop,he,(hr u).2,hoffer u hu,hvalid]⟩

/-- Reviewer-facing progress uses only the complete mathematical queue relation and free space. -/
theorem write_progress_queue {q : List (BitVec w)} (hqueue : QueueRelation s q)
    (xs : Nat → Input k w)
    (hr : ∀ t, (xs t).writeReset = false ∧ (xs t).readReset = false)
    (hf : QueueSpec.EdgeFair gap (fun t => (xs t).writeEdge))
    (hcredit : q.length < 2^k)
    (hoffer : ∀ t, t < 3*gap → (xs t).valid = true) :
    ∃ u, u < 3*gap ∧ push (stateFrom s xs u) (xs u) = true := by
  obtain ⟨g,history,hs,hc,hm,rfl⟩ := hqueue
  exact write_progress ⟨g,hs,hc⟩ xs hr hf (by simpa only [queue_length] using hcredit) hoffer

/-- Every pending mathematical queue head can be consumed within the stated fairness bound. -/
theorem read_progress_queue {q : List (BitVec w)} (hqueue : QueueRelation s q)
    (xs : Nat → Input k w)
    (hr : ∀ t, (xs t).writeReset = false ∧ (xs t).readReset = false)
    (hf : QueueSpec.EdgeFair gap (fun t => (xs t).readEdge))
    (hdata : q ≠ [])
    (hoffer : ∀ t, t < 3*gap → (xs t).ready = true) :
    ∃ u, u < 3*gap ∧ pop (stateFrom s xs u) (xs u) = true := by
  obtain ⟨g,history,hs,hc,hm,rfl⟩ := hqueue
  apply read_progress ⟨g,hs,hc⟩ xs hr hf _ hoffer
  change g.read < g.written
  have hlen : (queue g history).length ≠ 0 := by
    intro hz
    exact hdata (List.length_eq_zero_iff.mp hz)
  simp only [queue_length] at hlen
  omega

end HDLean.AsyncFifo
