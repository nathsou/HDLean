import Designs.Fifo.CircularProof
import Designs.CircularFifo.Interface
import HDLean.Semantics.Reset
import Init.Data.List.Range

set_option backward.isDefEq.respectTransparency false
namespace HDLean.Fifo.Circular

/-- The reviewed list queue corresponding to the live interval of physical RAM. -/
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

private theorem record_slice (g : Ghost) (history : Nat → BitVec w)
    (s : State w k) (i : Input (BitVec w)) (start count : Nat)
    (h : start+count ≤ g.written) :
    slice (g.record history s i) start count = slice history start count := by
  apply slice_congr
  intro n hn hlt
  have he : n ≠ g.written := by omega
  simp [Ghost.record,he]

/-- One physical step performs exactly the reviewed list-queue transition. -/
theorem queue_next {g : Ghost} {s : State w k} {history : Nat → BitVec w}
    (h : g.Safe (2^k)) (hc : g.Controls s) (i : Input (BitVec w)) :
    queue (g.advance (push s i) (pop s i)) (g.record history s i) =
      (Fifo.spec (BitVec w) (2^k)).next (queue g history) i := by
  have hp := push_has_space hc (i:=i)
  have hd := pop_has_data hc (i:=i)
  have hvalid : (s.count != 0) = !(queue g history).isEmpty := by
    have hz : s.count = 0 ↔ queue g history = [] := by
      rw [← List.length_eq_zero_iff, queue_length, ← hc.2]
      exact ⟨fun h => by simp [h], fun h => BitVec.eq_of_toNat_eq (by simpa using h)⟩
    apply Bool.eq_iff_iff.mpr
    simpa only [bne_iff_ne, Bool.not_eq_true', List.isEmpty_eq_false_iff] using not_congr hz
  have hpush : (i.enqValid && decide ((queue g history).length < 2^k)) = push s i := by
    simp [push,queue_length,←hc.2]
  have hpop : (i.deqReady && !(queue g history).isEmpty) = pop s i := by
    rw [← hvalid]; rfl
  change queue _ _ = if i.enqValid && decide ((queue g history).length < 2^k) then
    (if i.deqReady && !(queue g history).isEmpty then (queue g history).tail else queue g history) ++ [i.enqData]
    else (if i.deqReady && !(queue g history).isEmpty then (queue g history).tail else queue g history)
  rw [hpush,hpop]
  change slice _ _ _ = _
  cases he : push s i <;> cases ho : pop s i <;>
    simp only [Bool.false_eq_true,↓reduceIte,Ghost.advance,Nat.add_zero]
  · simp [Ghost.record,he,queue,slice]
  · have hrd := hd ho
    have hlen : g.written-(g.read+1) = (g.written-g.read)-1 := by omega
    rw [hlen,record_slice g history s i _ _ (by omega)]
    exact (slice_tail history g.read (g.written-g.read)).symm
  · have hlen : g.written+1-g.read = (g.written-g.read)+1 := by have := h.1; omega
    rw [hlen,slice_snoc,record_slice g history s i _ _ (by omega)]
    have heq : g.read+(g.written-g.read)=g.written := Nat.add_sub_of_le h.1
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

/-- A physical state is related to the complete mathematical queue, not just a control property. -/
def QueueRelation (s : State w k) (q : List (BitVec w)) : Prop :=
  ∃ (g : Ghost) (history : Nat → BitVec w), g.Safe (2^k) ∧ g.Controls s ∧
    g.Memory history s ∧ q = queue g history

variable {w k : Nat} {s : State w k} {q : List (BitVec w)}

theorem queue_relation_reset (s : State w k) (i : Input (BitVec w)) :
    QueueRelation ((machine w k).next s (i,true)) [] := by
  refine ⟨⟨0,0⟩,fun _ => 0,?_,?_,?_,?_⟩
  · simp [Ghost.Safe]
  · simp [Ghost.Controls,machine]
  · simp [Ghost.Memory]
  · simp [queue]

theorem queue_relation_step (h : QueueRelation s q) (i : Input (BitVec w)) :
    QueueRelation ((machine w k).next s (i,false)) ((Fifo.spec (BitVec w) (2^k)).next q i) := by
  obtain ⟨g,history,hs,hc,hm,rfl⟩ := h
  refine ⟨g.advance (push s i) (pop s i),g.record history s i,
    advance_safe hs hc,controls_next hs hc i,memory_next hs hc hm,?_⟩
  exact (queue_next hs hc i).symm

theorem queue_relation_out (h : QueueRelation s q) :
    (machine w k).out s = (Fifo.spec (BitVec w) (2^k)).out q := by
  obtain ⟨g,history,hs,hc,hm,rfl⟩ := h
  cases hn : g.written-g.read with
  | zero =>
    have hc0 : s.count = 0 := BitVec.eq_of_toNat_eq (by simpa [hn] using hc.2)
    have hq : queue g history = [] := by simp [queue,hn]
    simp [machine,Fifo.spec,hc0,hq]
  | succ n =>
    have hcn : s.count ≠ 0 := by
      intro hz
      have he := hc.2
      simp [hz,hn] at he
    have hdata : s.buffer s.head = history g.read := by
      rw [hc.1]
      exact hm _ (Nat.le_refl _) (by omega)
    have hq : queue g history = history g.read :: slice history (g.read+1) n := by
      simp [queue,hn,List.range'_succ,slice]
    simp [machine,Fifo.spec,hq,hdata,hc.2,hn]
    exact hcn

/-- Every physical circular-buffer trace refines the reviewed queue, from arbitrary RAM and registers. -/
theorem trace_refines_queue (w k : Nat) :
    RefinesAfterReset (machine w k) (Fifo.spec (BitVec w) (2^k)) id 1 := by
  apply refinesAfterReset_of_simulation _ _ _ _ QueueRelation
  · intro s xs hr
    change QueueRelation ((machine w k).next s (xs 0)) []
    rw [show xs 0 = ((xs 0).1,true) from Prod.ext rfl (hr 0 (by omega))]
    exact queue_relation_reset _ _
  · intro s q i h
    exact queue_relation_step h i
  · intro s q h
    exact queue_relation_out h

namespace Physical

/-- Headline refinement names the synthesizable AST and the complete, general-depth queue. -/
theorem hardware_refines_queue (k w : Nat) :
    RefinesAfterReset ((hardware k w).denote (hardware_moore k w)) (queueSpec k w) observe 1 := by
  apply refinesAfterReset_of_simulation _ _ _ _ (fun s q => QueueRelation (decode s) q)
  · intro s xs hr
    change QueueRelation (decode ((hardware k w).next s (xs 0))) []
    rw [show xs 0 = ((xs 0).1,(xs 0).2) from rfl,decode_next]
    rw [hr 0 (by omega)]
    exact queue_relation_reset _ _
  · intro s q i h
    change QueueRelation (decode ((hardware k w).next s (i,false))) _
    rw [decode_next]
    exact queue_relation_step h _
  · intro s q h
    change observe ((hardware k w).evalOutput s (fun _ => false)) = _
    rw [decode_output]
    exact queue_relation_out h

end Physical

end HDLean.Fifo.Circular
