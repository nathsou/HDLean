import Designs.AsyncFifo.Proof
import Designs.AsyncFifo.Spec
import Init.Data.List.Range

set_option backward.isDefEq.respectTransparency false
namespace HDLean.AsyncFifo

/-- Complete mathematical contents of the live physical RAM interval. -/
def queue (g : Ghost) (history : Nat → BitVec w) : List (BitVec w) :=
  (List.range' g.read (g.written-g.read)).map history

private def slice (history : Nat → α) (start count : Nat) : List α :=
  (List.range' start count).map history

@[simp] private theorem slice_length (history : Nat → α) (start count : Nat) :
    (slice history start count).length = count := by simp [slice]

private theorem slice_snoc (history : Nat → α) (start count : Nat) :
    slice history start (count+1) = slice history start count ++ [history (start+count)] := by
  unfold slice
  rw [← List.range'_append_1]
  simp [List.range'_succ]

private theorem slice_tail (history : Nat → α) (start count : Nat) :
    (slice history start count).tail = slice history (start+1) (count-1) := by
  unfold slice
  rw [← List.map_tail, List.tail_range']

private theorem slice_congr (a b : Nat → α) (start count : Nat)
    (h : ∀ n, start ≤ n → n < start+count → a n = b n) :
    slice a start count = slice b start count := by
  apply List.map_congr_left
  intro n hn
  obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hn
  exact h _ (by omega) (by omega)


@[simp] theorem queue_length (g : Ghost) (history : Nat → BitVec w) :
    (queue g history).length = g.written-g.read := by simp [queue]

def observe (s : State k w) : Fifo.Output (BitVec w) :=
  ⟨enqReady s,deqValid s,if deqValid s then some (data s) else none⟩

def queueInput (i : Input k w) : QueueSpec.Input (BitVec w) :=
  ⟨i.writeEdge,i.readEdge,i.valid,i.data,i.ready⟩

variable {g : Ghost} {s : State k w} {history : Nat → BitVec w}

theorem ready_has_space (h : g.Safe (2^k)) (hc : g.Controls s) (he : enqReady s = true) :
    g.written-g.read < 2^k := by
  let offer : Input k w := ⟨true,false,false,false,true,0,false,0,0⟩
  have hp : push s offer = true := by simp [push,offer,he]
  have hs := push_has_space h hc hp
  unfold Ghost.Safe at h
  omega

theorem valid_has_data (h : g.Safe (2^k)) (hc : g.Controls s) (he : deqValid s = true) :
    g.read < g.written := by
  let offer : Input k w := ⟨false,true,false,false,false,0,true,0,0⟩
  have hp : pop s offer = true := by simp [pop,offer,he]
  have hs := pop_has_data h hc hp
  unfold Ghost.Safe at h
  omega

/-- Every physical flag and observed word obeys the relational mathematical queue model. -/
theorem queue_allowed (h : g.Safe (2^k)) (hc : g.Controls s) (hm : g.Memory history s) :
    QueueSpec.Allowed (2^k) (queue g history) (observe s) := by
  refine ⟨?_,?_,?_⟩
  · intro he
    simpa only [queue_length] using ready_has_space h hc he
  · intro he
    have hd := valid_has_data h hc he
    intro hq
    have hl := congrArg List.length hq
    simp only [queue_length,List.length_nil] at hl
    omega
  · change (if deqValid s then some (data s) else none) = _
    cases he : deqValid s with
    | false => simp [observe,he]
    | true =>
      have hd := valid_has_data h hc he
      let offer : Input k w := ⟨false,true,false,false,false,0,true,0,0⟩
      have hp : pop s offer = true := by simp [pop,offer,he]
      have hv := data_is_oldest h hc hm hp
      have hn : ∃ n, g.written-g.read = n+1 := ⟨g.written-g.read-1,by omega⟩
      obtain ⟨n,hn⟩ := hn
      simp [queue,hn,List.range'_succ,he,observe,hv]

private theorem record_slice (g : Ghost) (history : Nat → BitVec w)
    (s : State k w) (i : Input k w) (start count : Nat)
    (h : start+count ≤ g.written) :
    slice (g.record history s i) start count = slice history start count := by
  apply slice_congr
  intro n hn hlt
  exact record_preserves_committed (by omega)

/-- Advancing absolute transfer counts reconstructs exactly one list-queue step. -/
theorem queue_next {g' : Ghost} (h : g.Safe (2^k)) (hc : g.Controls s) (i : Input k w)
    (hwr : i.writeReset = false) (hrr : i.readReset = false)
    (hgw : g'.written = g.written + (if push s i then 1 else 0))
    (hgr : g'.read = g.read + (if pop s i then 1 else 0)) :
    queue g' (g.record history s i) = QueueSpec.next (queue g history) (queueInput i) (observe s) := by
  have hd : pop s i = true → g.read < g.written := by
    intro hp
    simp only [pop,Bool.and_eq_true] at hp
    exact valid_has_data h hc hp.2
  have hsafe := g.occupancy_bound h
  have hpush : (i.writeEdge && i.valid && enqReady s) = push s i := by simp [push,hwr]
  have hpop : (i.readEdge && i.ready && deqValid s) = pop s i := by simp [pop,hrr]
  simp only [QueueSpec.next,queueInput,observe,hpush,hpop]
  change slice _ _ _ = _
  simp only [hgw,hgr]
  cases he : push s i <;> cases ho : pop s i <;>
    simp only [Bool.false_eq_true,↓reduceIte,Nat.add_zero]
  · simp [Ghost.record,he,queue,slice]
  · have hrd := hd ho
    have hlen : g.written-(g.read+1) = (g.written-g.read)-1 := by omega
    rw [hlen,record_slice g history s i _ _ (by omega)]
    exact (slice_tail history g.read (g.written-g.read)).symm
  · have hlen : g.written+1-g.read = (g.written-g.read)+1 := by omega
    rw [hlen,slice_snoc,record_slice g history s i _ _ (by omega)]
    have heq : g.read+(g.written-g.read)=g.written := Nat.add_sub_of_le hsafe.1
    rw [heq]
    simp [Ghost.record,he,queue,slice]
  · have hrd := hd ho
    have hlen : g.written+1-(g.read+1) = (g.written-(g.read+1))+1 := by omega
    rw [hlen,slice_snoc,record_slice g history s i _ _ (by omega)]
    have heq : g.read+1+(g.written-(g.read+1))=g.written := Nat.add_sub_of_le (by omega)
    rw [heq]
    rw [show g.written-(g.read+1)=(g.written-g.read)-1 by omega]
    rw [← slice_tail]
    simp [Ghost.record,he,queue,slice]

/-- The entire list queue is related to actual pointer and RAM contents. -/
def QueueRelation (s : State k w) (q : List (BitVec w)) : Prop :=
  ∃ (g : Ghost) (history : Nat → BitVec w), g.Safe (2^k) ∧ g.Controls s ∧
    g.Memory history s ∧ q = queue g history

variable {q : List (BitVec w)} {i : Input k w}

theorem queue_relation_reset (h : ResetProgress true true s) : QueueRelation s [] := by
  have he := reset_establishes_queue h (fun _ => (0 : BitVec w))
  exact ⟨Ghost.empty,fun _ => 0,he.1,he.2.1,he.2.2,by simp [queue,Ghost.empty]⟩

theorem queue_relation_step (h : QueueRelation s q)
    (hwr : i.writeReset = false) (hrr : i.readReset = false) :
    QueueRelation (next s i) (QueueSpec.next q (queueInput i) (observe s)) := by
  obtain ⟨g,history,hs,hc,hm,rfl⟩ := h
  obtain ⟨g',hs',hc',hm',hw,hr,_⟩ := step_refines_queue hs hc hm hwr hrr
  exact ⟨g',g.record history s i,hs',hc',hm',(queue_next hs hc i hwr hrr hw hr).symm⟩

theorem queue_relation_allowed (h : QueueRelation s q) : QueueSpec.Allowed (2^k) q (observe s) := by
  obtain ⟨g,history,hs,hc,hm,rfl⟩ := h
  exact queue_allowed hs hc hm

/-- Physical startup and every sampling-mask choice remain explicit in the trace. -/
def stateFrom (s : State k w) (xs : Nat → Input k w) : Nat → State k w
  | 0 => s
  | t+1 => next (stateFrom s xs t) (xs t)

def seenWrite (xs : Nat → Input k w) : Nat → Bool
  | 0 => false
  | t+1 => seenWrite xs t || (xs t).writeEdge

def seenRead (xs : Nat → Input k w) : Nat → Bool
  | 0 => false
  | t+1 => seenRead xs t || (xs t).readEdge

/-- Startup requires held reset and an actual reset edge in both independent domains. -/
def Startup (xs : Nat → Input k w) (release : Nat) : Prop :=
  (∀ t, t < release → (xs t).writeReset = true ∧ (xs t).readReset = true) ∧
  seenWrite xs release = true ∧ seenRead xs release = true

theorem reset_prefix (s : State k w) (xs : Nat → Input k w) (release : Nat)
    (h : ∀ t, t < release → (xs t).writeReset = true ∧ (xs t).readReset = true) :
    ResetProgress (seenWrite xs release) (seenRead xs release) (stateFrom s xs release) := by
  induction release with
  | zero => exact reset_progress_initial s
  | succ t ih =>
    have hp := h t (by omega)
    exact (reset_progress (ih (fun u hu => h u (by omega))) hp.1 hp.2).1

theorem stateFrom_shift (s : State k w) (xs : Nat → Input k w) (release t : Nat) :
    stateFrom (stateFrom s xs release) (fun n => xs (release+n)) t = stateFrom s xs (release+t) := by
  induction t with
  | zero => simp [stateFrom]
  | succ t ih => simp only [stateFrom,ih] <;> rfl

/-- Full list-queue trace refinement after held-reset startup, for arbitrary power-up,
independent/coincident edges, and every per-bit sampling-mask sequence. -/
theorem trace_refines_queue (s : State k w) (xs : Nat → Input k w) (release : Nat)
    (hstart : Startup xs release)
    (htraffic : ∀ t, release ≤ t → (xs t).writeReset = false ∧ (xs t).readReset = false) :
    let inputs := fun t => queueInput (xs (release+t))
    let outputs := fun t => observe (stateFrom s xs (release+t))
    QueueSpec.Trace (2^k) inputs outputs (QueueSpec.run inputs outputs) := by
  dsimp only
  have hzero : QueueRelation (stateFrom s xs release) [] := by
    apply queue_relation_reset
    have hp := reset_prefix s xs release hstart.1
    simpa only [hstart.2.1,hstart.2.2] using hp
  have hrel (t : Nat) : QueueRelation (stateFrom s xs (release+t))
      (QueueSpec.run (fun u => queueInput (xs (release+u)))
        (fun u => observe (stateFrom s xs (release+u))) t) := by
    induction t with
    | zero => simpa [QueueSpec.run] using hzero
    | succ t ih =>
      have hp := htraffic (release+t) (by omega)
      exact queue_relation_step ih hp.1 hp.2
  refine ⟨rfl,?_⟩
  intro t
  exact ⟨queue_relation_allowed (hrel t),rfl⟩

end HDLean.AsyncFifo
