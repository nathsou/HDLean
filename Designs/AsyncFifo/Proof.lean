import Designs.AsyncFifo.Model
import HDLean.Semantics.GrayProof
namespace HDLean.AsyncFifo

private theorem gray_fold (x acc : BitVec w) (n : Nat) :
    (List.range n).foldl (fun a j => a ^^^ (gray x >>> j)) acc =
      acc ^^^ x ^^^ (x >>> n) := by
  induction n with
  | zero => simp [BitVec.xor_assoc]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    simp only [gray, BitVec.ushiftRight_xor_distrib, ← BitVec.shiftRight_add]
    rw [Nat.add_comm 1 n]
    simp only [BitVec.xor_assoc, BitVec.xor_right_inj]
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The actual finite XOR decoder in the physical model inverts Gray encoding. -/
theorem ungray_gray (x : BitVec w) : ungray (gray x) = x := by
  rw [ungray, gray_fold]
  simp [BitVec.ushiftRight_eq_zero (Nat.le_refl w)]

/-- Adding the wrap bit toggles it, including arithmetic wraparound. -/
theorem add_wrap_bit (x : BitVec (k + 1)) :
    x + BitVec.ofNat (k + 1) (2^k) = x ^^^ BitVec.ofNat (k + 1) (2^k) := by
  have hc : ∀ i, i ≤ k → BitVec.carry i x (BitVec.ofNat (k + 1) (2^k)) false = false := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      rw [BitVec.carry_succ, ih (by omega)]
      have hb : (BitVec.ofNat (k+1) (2^k)).getLsbD i = false := by
        simp [BitVec.getLsbD_ofNat, show k ≠ i by omega]
      simp [hb, Bool.atLeastTwo]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_add hi, BitVec.getLsbD_xor, hc i (by omega)]
  simp

/-- Absolute counters are proof-only ghost state. They never enter synthesized hardware. -/
structure Ghost where
  written : Nat
  read : Nat
  writeFirst : Nat
  writeSecond : Nat
  readFirst : Nat
  readSecond : Nat
  deriving Repr

/-- Synchronizer snapshots are ordered and conservative in both directions. -/
def Ghost.Safe (g : Ghost) (capacity : Nat) : Prop :=
  g.readSecond ≤ g.readFirst ∧ g.readFirst ≤ g.read ∧
  g.read ≤ g.writeSecond ∧ g.writeSecond ≤ g.writeFirst ∧
  g.writeFirst ≤ g.written ∧ g.written ≤ g.readSecond + capacity

/-- Relate every actual control flop to an absolute pointer or Gray snapshot. -/
def Ghost.Controls (g : Ghost) (s : State k w) : Prop :=
  s.write = BitVec.ofNat (k+1) g.written ∧
  s.read = BitVec.ofNat (k+1) g.read ∧
  s.seenWrite.first = gray (BitVec.ofNat (k+1) g.writeFirst) ∧
  s.seenWrite.second = gray (BitVec.ofNat (k+1) g.writeSecond) ∧
  s.seenRead.first = gray (BitVec.ofNat (k+1) g.readFirst) ∧
  s.seenRead.second = gray (BitVec.ofNat (k+1) g.readSecond)

variable {g : Ghost} {s : State k w} {i : Input k w}

theorem Ghost.occupancy_bound (h : g.Safe capacity) :
    g.read ≤ g.written ∧ g.written - g.read ≤ capacity := by
  unfold Ghost.Safe at h
  omega

/-- A physically accepted write always has a free slot, even with stale snapshots. -/
theorem push_has_space (h : g.Safe (2^k)) (hc : g.Controls s) (hp : push s i = true) :
    g.written < g.readSecond + 2^k := by
  have hr : enqReady s = true := by simp only [push, Bool.and_eq_true] at hp; exact hp.2
  unfold enqReady at hr
  rw [hc.1, hc.2.2.2.2.2, ungray_gray] at hr
  have hne : BitVec.ofNat (k+1) g.written ≠
      BitVec.ofNat (k+1) g.readSecond ^^^ BitVec.ofNat (k+1) (2^k) := by simpa using hr
  have hu := h.2.2.2.2.2
  by_cases hn : g.written < g.readSecond + 2^k
  · exact hn
  have he : g.written = g.readSecond + 2^k := by omega
  exact False.elim (hne (by rw [he, BitVec.ofNat_add, add_wrap_bit]))

/-- A physically accepted read always names a committed word. -/
theorem pop_has_data (h : g.Safe (2^k)) (hc : g.Controls s) (hp : pop s i = true) :
    g.read < g.writeSecond := by
  have hv : deqValid s = true := by simp only [pop, Bool.and_eq_true] at hp; exact hp.2
  unfold deqValid at hv
  rw [hc.2.1, hc.2.2.2.1, ungray_gray] at hv
  have hne : BitVec.ofNat (k+1) g.read ≠ BitVec.ofNat (k+1) g.writeSecond := by simpa using hv
  have hl := h.2.2.1
  by_cases hn : g.read < g.writeSecond
  · exact hn
  have he : g.read = g.writeSecond := by omega
  exact False.elim (hne (congrArg (BitVec.ofNat (k+1)) he))

/-- Logical transfers and synchronizer sampling advance only on the relevant edge. -/
def Ghost.advance (g : Ghost) (writeEdge readEdge enq deq sampleWriteNew sampleReadNew : Bool) : Ghost :=
  let wp := g.written + if enq then 1 else 0
  let rp := g.read + if deq then 1 else 0
  { written := wp, read := rp
    writeFirst := if readEdge then (if sampleWriteNew then wp else g.written) else g.writeFirst
    writeSecond := if readEdge then g.writeFirst else g.writeSecond
    readFirst := if writeEdge then (if sampleReadNew then rp else g.read) else g.readFirst
    readSecond := if writeEdge then g.readFirst else g.readSecond }

/-- No frequency ratio or relative edge ordering is required for pointer safety. -/
theorem Ghost.advance_safe (h : g.Safe capacity)
    (he : enq = true → writeEdge = true ∧ g.written < g.readSecond + capacity)
    (hd : deq = true → readEdge = true ∧ g.read < g.writeSecond) :
    (g.advance writeEdge readEdge enq deq sampleWriteNew sampleReadNew).Safe capacity := by
  cases writeEdge <;> cases readEdge <;> cases enq <;> cases deq <;>
    cases sampleWriteNew <;> cases sampleReadNew <;>
    simp_all [Ghost.Safe, Ghost.advance] <;> omega

private theorem sample_same (x mask : BitVec w) : sampleBits x x mask = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [sampleBits, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hj,
    decide_true, Bool.true_and]
  cases x.getLsbD j <;> cases mask.getLsbD j <;> decide

/-- Even during a transfer, every sampled pointer has an absolute endpoint witness. -/
theorem sample_absolute (n : Nat) (move : Bool) (mask : BitVec (k+1)) :
    ∃ choice : Bool,
      sampleBits (gray (BitVec.ofNat (k+1) n))
        (gray (BitVec.ofNat (k+1) (n + if move then 1 else 0))) mask =
      gray (BitVec.ofNat (k+1) (if choice then n + (if move then 1 else 0) else n)) := by
  cases move with
  | false => exact ⟨false, by simp [sample_same]⟩
  | true =>
    simp only [↓reduceIte, BitVec.ofNat_add]
    rcases sample_gray_increment (BitVec.ofNat (k+1) n) mask (by omega) with h | h
    · exact ⟨false, by simpa using h⟩
    · exact ⟨true, by simpa [BitVec.ofNat_add] using h⟩

/-- The two physical synchronizer stages refine ordered absolute endpoint sampling. -/
theorem next_controls (hc : g.Controls s)
    (hwr : i.writeReset = false) (hrr : i.readReset = false) :
    ∃ sw sr : Bool,
      (g.advance i.writeEdge i.readEdge (push s i) (pop s i) sw sr).Controls (next s i) := by
  obtain ⟨sw, hsw⟩ := sample_absolute g.written (push s i) i.readMask
  obtain ⟨sr, hsr⟩ := sample_absolute g.read (pop s i) i.writeMask
  have hw : (if push s i then s.write + 1 else s.write) =
      BitVec.ofNat (k+1) (g.written + if push s i then 1 else 0) := by
    cases hp : push s i <;> simp [hc.1, BitVec.ofNat_add]
  have hr : (if pop s i then s.read + 1 else s.read) =
      BitVec.ofNat (k+1) (g.read + if pop s i then 1 else 0) := by
    cases hp : pop s i <;> simp [hc.2.1, BitVec.ofNat_add]
  refine ⟨sw, sr, ?_⟩
  unfold Ghost.Controls Ghost.advance next
  simp only [hwr, hrr, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  refine ⟨hw, hr, ?_, ?_, ?_, ?_⟩
  · cases he : i.readEdge with
    | false => simpa using hc.2.2.1
    | true =>
      simp only [↓reduceIte]
      rw [hw, hc.1]
      exact hsw
  · cases he : i.readEdge <;> simp [hc.2.2.1, hc.2.2.2.1]
  · cases he : i.writeEdge with
    | false => simpa using hc.2.2.2.2.1
    | true =>
      simp only [↓reduceIte]
      rw [hr, hc.2.1]
      exact hsr
  · cases he : i.writeEdge <;> simp [hc.2.2.2.2.1, hc.2.2.2.2.2]

/-- One physical step preserves bounded occupancy for arbitrary edges and masks. -/
theorem next_safe (h : g.Safe (2^k)) (hc : g.Controls s)
    (hwr : i.writeReset = false) (hrr : i.readReset = false) :
    ∃ g' : Ghost, g'.Safe (2^k) ∧ g'.Controls (next s i) ∧
      g'.written = g.written + (if push s i then 1 else 0) ∧
      g'.read = g.read + (if pop s i then 1 else 0) := by
  obtain ⟨sw, sr, hs⟩ := next_controls hc hwr hrr
  refine ⟨g.advance i.writeEdge i.readEdge (push s i) (pop s i) sw sr, ?_, hs, rfl, rfl⟩
  apply Ghost.advance_safe h
  · intro hp
    have he : i.writeEdge = true := by simp only [push, Bool.and_eq_true] at hp; exact hp.1.1.1
    exact ⟨he, push_has_space h hc hp⟩
  · intro hp
    have he : i.readEdge = true := by simp only [pop, Bool.and_eq_true] at hp; exact hp.1.1.1
    exact ⟨he, pop_has_data h hc hp⟩

private theorem mod_injective_window {a b d : Nat} (hab : a ≤ b) (hbd : b < a + d)
    (he : a % d = b % d) : a = b := by
  have ha := Nat.mod_add_div a d
  have hb := Nat.mod_add_div b d
  by_cases hq : a / d = b / d
  · rw [hq, he] at ha
    omega
  have hl : a / d ≤ b / d := Nat.div_le_div_right hab
  have hm := Nat.mul_le_mul_left d (show a / d + 1 ≤ b / d by omega)
  rw [Nat.mul_add, Nat.mul_one] at hm
  omega

/-- Every live absolute queue position resides at its circular physical address. -/
def Ghost.Memory (g : Ghost) (history : Nat → BitVec w) (s : State k w) : Prop :=
  ∀ n, g.read ≤ n → n < g.written → s.memory (BitVec.ofNat k n) = history n

/-- The append-only logical history advances only on a physically accepted write. -/
def Ghost.record (g : Ghost) (history : Nat → BitVec w) (s : State k w) (i : Input k w) : Nat → BitVec w :=
  fun n => if push s i && n == g.written then i.data else history n

/-- An accepted dequeue returns exactly the oldest not-yet-read logical word. -/
theorem data_is_oldest (h : g.Safe (2^k)) (hc : g.Controls s)
    (hm : g.Memory history s) (hp : pop s i = true) : data s = history g.read := by
  have hr := pop_has_data h hc hp
  have hw : g.read < g.written := by unfold Ghost.Safe at h; omega
  unfold data
  rw [hc.2.1, BitVec.setWidth_ofNat_of_le (by omega)]
  exact hm _ (Nat.le_refl _) hw

/-- A concurrent push cannot overwrite any unread older word. -/
theorem write_address_fresh (h : g.Safe (2^k)) (hp : push s i = true)
    (hc : g.Controls s) (hn : g.read ≤ n) (hw : n < g.written) :
    BitVec.ofNat k n ≠ s.write.setWidth k := by
  intro he
  rw [hc.1, BitVec.setWidth_ofNat_of_le (by omega)] at he
  have hemod := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat] at hemod
  have hs := push_has_space h hc hp
  have hsnap : g.readSecond ≤ g.read := by unfold Ghost.Safe at h; omega
  have heq := mod_injective_window (Nat.le_of_lt hw) (by omega) hemod
  omega

/-- The physical memory update preserves the complete live queue contents. -/
theorem next_memory {g' : Ghost} (h : g.Safe (2^k)) (hc : g.Controls s) (hm : g.Memory history s)
    (hgw : g'.written = g.written + (if push s i then 1 else 0))
    (hgr : g'.read = g.read + (if pop s i then 1 else 0)) :
    g'.Memory (g.record history s i) (next s i) := by
  intro n hn hw
  have hnold : g.read ≤ n := by rw [hgr] at hn; split at hn <;> omega
  cases hp : push s i with
  | false =>
    have hnwrite : n < g.written := by rw [hgw] at hw; simpa [hp] using hw
    simpa [next, Ghost.record, hp] using hm n hnold hnwrite
  | true =>
    have hnwrite : n ≤ g.written := by rw [hgw] at hw; simp [hp] at hw; omega
    by_cases he : n = g.written
    · subst n
      simp [next, Ghost.record, hp, hc.1, BitVec.setWidth_ofNat_of_le (show k ≤ k+1 by omega)]
    · have hlt : n < g.written := by omega
      have hf := write_address_fresh h hp hc hnold hlt
      simpa [next, Ghost.record, hp, he, hf] using hm n hnold hlt

/-- A reset-domain acknowledgement says all of that domain's control flops reset. -/
def ResetProgress (writeSeen readSeen : Bool) (s : State k w) : Prop :=
  (writeSeen = true → s.write = 0 ∧ s.seenRead.first = 0 ∧ s.seenRead.second = 0) ∧
  (readSeen = true → s.read = 0 ∧ s.seenWrite.first = 0 ∧ s.seenWrite.second = 0)

/-- Holding common reset permits unrelated domain edges; memory remains arbitrary. -/
theorem reset_progress (h : ResetProgress writeSeen readSeen s)
    (hwr : i.writeReset = true) (hrr : i.readReset = true) :
    ResetProgress (writeSeen || i.writeEdge) (readSeen || i.readEdge) (next s i) ∧
      (next s i).memory = s.memory := by
  cases hw : i.writeEdge <;> cases hr : i.readEdge <;>
    simp_all [ResetProgress, next, push, pop]

/-- No reset observations are assumed at arbitrary power-up. -/
theorem reset_progress_initial (s : State k w) : ResetProgress false false s := by
  simp [ResetProgress]

def Ghost.empty : Ghost := ⟨0, 0, 0, 0, 0, 0⟩

/-- Release reset after each domain has seen it at least once, without clearing memory. -/
theorem reset_establishes_queue (h : ResetProgress true true s) (history : Nat → BitVec w) :
    Ghost.empty.Safe (2^k) ∧ Ghost.empty.Controls s ∧ Ghost.empty.Memory history s := by
  have h := And.intro (h.1 rfl) (h.2 rfl)
  refine ⟨by simp [Ghost.Safe, Ghost.empty], ?_, ?_⟩
  · rcases h with ⟨⟨hw, hr1, hr2⟩, ⟨hr, hw1, hw2⟩⟩
    simp [Ghost.Controls, Ghost.empty, gray, hw, hr, hr1, hr2, hw1, hw2]
  · intro n hn hw
    simp [Ghost.empty] at hw

/-- The complete queue simulation step: control, contents, transfer counts and read value.
Both resets stay deasserted during traffic; independent reassertion is not specified. -/
theorem step_refines_queue (h : g.Safe (2^k)) (hc : g.Controls s) (hm : g.Memory history s)
    (hwr : i.writeReset = false) (hrr : i.readReset = false) :
    ∃ g' : Ghost, g'.Safe (2^k) ∧ g'.Controls (next s i) ∧
      g'.Memory (g.record history s i) (next s i) ∧
      g'.written = g.written + (if push s i then 1 else 0) ∧
      g'.read = g.read + (if pop s i then 1 else 0) ∧
      (pop s i = true → data s = history g.read) := by
  obtain ⟨g', hs, hctrl, hw, hr⟩ := next_safe h hc hwr hrr
  exact ⟨g', hs, hctrl, next_memory h hc hm hw hr, hw, hr, data_is_oldest h hc hm⟩

theorem record_preserves_committed (hn : n < g.written) :
    g.record history s i n = history n := by
  simp [Ghost.record, show n ≠ g.written by omega]

theorem record_newest (hp : push s i = true) : g.record history s i g.written = i.data := by
  simp [Ghost.record, hp]

end HDLean.AsyncFifo
