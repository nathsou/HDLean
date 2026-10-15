import Designs.Fifo.Circular

set_option backward.isDefEq.respectTransparency false
namespace HDLean.Fifo.Circular

/-- Absolute positions describe the logical queue without modulo ambiguity. -/
structure Ghost where
  read : Nat
  written : Nat

def Ghost.Safe (g : Ghost) (capacity : Nat) : Prop :=
  g.read ≤ g.written ∧ g.written ≤ g.read+capacity

def Ghost.Controls (g : Ghost) (s : State w k) : Prop :=
  s.head = BitVec.ofNat k g.read ∧ s.count.toNat = g.written-g.read

def Ghost.Memory (g : Ghost) (history : Nat → BitVec w) (s : State w k) : Prop :=
  ∀ n, g.read ≤ n → n < g.written → s.buffer (BitVec.ofNat k n) = history n

def push (s : State w k) (i : Input (BitVec w)) : Bool :=
  i.enqValid && decide (s.count.toNat < 2^k)
def pop (s : State w k) (i : Input (BitVec w)) : Bool :=
  i.deqReady && s.count != 0

def Ghost.advance (g : Ghost) (enq deq : Bool) : Ghost :=
  ⟨g.read+(if deq then 1 else 0),g.written+(if enq then 1 else 0)⟩
def Ghost.record (g : Ghost) (history : Nat → BitVec w) (s : State w k) (i : Input (BitVec w)) :=
  fun n => if push s i && n == g.written then i.enqData else history n

variable {w k : Nat} {g : Ghost} {s : State w k} {i : Input (BitVec w)}

theorem push_has_space (hc : g.Controls s) (hp : push s i = true) :
    g.written-g.read < 2^k := by
  simp only [push, Bool.and_eq_true, decide_eq_true_eq] at hp
  simpa [← hc.2] using hp.2

theorem pop_has_data (hc : g.Controls s) (hp : pop s i = true) :
    g.read < g.written := by
  simp only [pop, Bool.and_eq_true, bne_iff_ne] at hp
  have hn : s.count.toNat ≠ 0 := by
    intro hz
    exact hp.2 (BitVec.eq_of_toNat_eq (by simpa using hz))
  rw [hc.2] at hn
  omega

theorem advance_safe (h : g.Safe (2^k)) (hc : g.Controls s) :
    (g.advance (push s i) (pop s i)).Safe (2^k) := by
  have hp := push_has_space hc (i:=i)
  have hd := pop_has_data hc (i:=i)
  cases he : push s i <;> cases ho : pop s i <;>
    simp_all [Ghost.Safe, Ghost.advance] <;> omega

private theorem capacity_fits (k : Nat) : 2^k < 2^(k+1) := by
  have := Nat.two_pow_pos k
  simp only [Nat.pow_succ, Nat.mul_two]
  omega

/-- Physical modular count arithmetic agrees with the bounded absolute occupancy. -/
theorem count_next (h : g.Safe (2^k)) (hc : g.Controls s) (i : Input (BitVec w)) :
    ((machine w k).next s (i,false)).count.toNat =
      (g.advance (push s i) (pop s i)).written - (g.advance (push s i) (pop s i)).read := by
  have hp := push_has_space hc (i:=i)
  have hd := pop_has_data hc (i:=i)
  have hf := capacity_fits k
  unfold Ghost.Safe at h
  change (s.count + (if push s i then 1 else 0) - (if pop s i then 1 else 0)).toNat = _
  cases he : push s i <;> cases ho : pop s i <;>
    simp [Ghost.advance]
  · exact hc.2
  · have hdv := hd ho
    have hx : 2^(k+1)-1+s.count.toNat = 2^(k+1)+(s.count.toNat-1) := by rw [hc.2]; omega
    rw [hx, Nat.add_mod_left, Nat.mod_eq_of_lt (by rw [hc.2]; omega),hc.2]
    omega
  · have hpv := hp he
    rw [Nat.mod_eq_of_lt (by rw [hc.2]; omega),hc.2]
    omega
  · have hpv := hp he
    have hx : 2^(k+1)-1+(s.count.toNat+1) = 2^(k+1)+s.count.toNat := by omega
    rw [hx,Nat.add_mod_left,Nat.mod_eq_of_lt (by rw [hc.2]; omega),hc.2]

theorem controls_next (h : g.Safe (2^k)) (hc : g.Controls s) (i : Input (BitVec w)) :
    (g.advance (push s i) (pop s i)).Controls ((machine w k).next s (i,false)) := by
  constructor
  · change (if pop s i then s.head+1 else s.head) = _
    cases hd : pop s i <;> simp [Ghost.advance,hc.1,BitVec.ofNat_add]
  · exact count_next h hc i

private theorem tail_address (h : g.Safe (2^k)) (hc : g.Controls s) :
    s.head+s.count.setWidth k = BitVec.ofNat k g.written := by
  have hcnt : s.count.setWidth k = BitVec.ofNat k (g.written-g.read) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth,hc.2]
  rw [hc.1,hcnt,←BitVec.ofNat_add,Nat.add_sub_of_le h.1]

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

theorem write_address_fresh (h : g.Safe (2^k)) (hc : g.Controls s) (hp : push s i = true)
    (hn : g.read ≤ n) (hw : n < g.written) :
    (BitVec.ofNat k n) ≠ s.head+s.count.setWidth k := by
  rw [tail_address h hc]
  intro he
  have hnmod := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat] at hnmod
  have hpv := push_has_space hc hp
  have heq := mod_injective_window (Nat.le_of_lt hw) (by have := h.1; omega) hnmod
  omega

theorem data_is_oldest (hc : g.Controls s) (hm : g.Memory history s) (hp : pop s i = true) :
    s.buffer s.head = history g.read := by
  rw [hc.1]
  exact hm _ (Nat.le_refl _) (pop_has_data hc hp)

theorem memory_next (h : g.Safe (2^k)) (hc : g.Controls s) (hm : g.Memory history s) :
    (g.advance (push s i) (pop s i)).Memory (g.record history s i) ((machine w k).next s (i,false)) := by
  intro n hn hw
  have hnold : g.read ≤ n := by
    change g.read+(if pop s i then 1 else 0) ≤ n at hn
    omega
  cases hp : push s i with
  | false =>
    have hlt : n < g.written := by simpa [Ghost.advance,hp] using hw
    have hpb := hp
    simp only [push] at hpb
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hpb
    rcases hpb with hpb | hpb <;> simpa [machine,Ghost.record,push,hpb] using hm n hnold hlt
  | true =>
    have hnle : n ≤ g.written := by simp [Ghost.advance,hp] at hw; omega
    by_cases he : n = g.written
    · subst n
      have hpb := hp
      simp only [push, Bool.and_eq_true, decide_eq_true_eq] at hpb
      simp [machine,tail_address h hc,Ghost.record,push,hpb.1,hpb.2]
    · have hlt : n < g.written := by omega
      have hf := write_address_fresh h hc hp hnold hlt
      have hpb := hp
      simp only [push, Bool.and_eq_true, decide_eq_true_eq] at hpb
      simpa [machine,Ghost.record,push,hpb,he,hf] using hm n hnold hlt

/-- No reset value is imposed on storage; one reset edge establishes an empty queue. -/
theorem reset_establishes_queue (s : State w k) (i : Input (BitVec w)) (history : Nat → BitVec w) :
    let zero : Ghost := ⟨0,0⟩
    zero.Safe (2^k) ∧ zero.Controls ((machine w k).next s (i,true)) ∧
      zero.Memory history ((machine w k).next s (i,true)) := by
  simp [Ghost.Safe,Ghost.Controls,Ghost.Memory,machine]

/-- Every accepted enqueue appends one word, every dequeue consumes the oldest
word, and no unread physical slot is overwritten, for all widths and capacities. -/
theorem step_refines_queue (h : g.Safe (2^k)) (hc : g.Controls s) (hm : g.Memory history s) :
    let g' := g.advance (push s i) (pop s i)
    g'.Safe (2^k) ∧ g'.Controls ((machine w k).next s (i,false)) ∧
      g'.Memory (g.record history s i) ((machine w k).next s (i,false)) ∧
      (pop s i = true → s.buffer s.head = history g.read) :=
  ⟨advance_safe h hc,controls_next h hc i,memory_next h hc hm,data_is_oldest hc hm⟩

end HDLean.Fifo.Circular
