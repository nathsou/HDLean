import Designs.Fifo.CircularProof
import HDLean.Lib.Select
import HDLean.Core.WordBank

set_option backward.isDefEq.respectTransparency false
namespace HDLean.Fifo.Circular.Physical
open WordExpr

def bits (k w : Nat) := max (k+1) w
def entries (k : Nat) := 2+2^k
abbrev W (k w n : Nat) := WordExpr 0 (w+2) (entries k * bits k w) n
abbrev E (k w : Nat) := Expr 0 (w+2) (entries k * bits k w)
def word (k w : Nat) (j : Fin (entries k)) : W k w (bits k w) := bankWord j

def head (k w : Nat) : W k w k := WordExpr.setWidth (word k w ⟨0,by have := Nat.two_pow_pos k; unfold entries; omega⟩) k
def count (k w : Nat) : W k w (k+1) := WordExpr.setWidth (word k w ⟨1,by have := Nat.two_pow_pos k; unfold entries; omega⟩) (k+1)
def memory (k w : Nat) (a : Fin (2^k)) : W k w w :=
  WordExpr.setWidth (word k w ⟨2+a.val, by have := a.isLt; unfold entries; omega⟩) w

def ready (k w : Nat) : E k w := ult (count k w) (literal (BitVec.ofNat (k+1) (2^k)))
def valid (k w : Nat) : E k w := .inv (equal (count k w) (literal 0))
def enq (k w : Nat) : E k w := .and (.input ⟨0,by omega⟩) (ready k w)
def deq (k w : Nat) : E k w := .and (.input ⟨1,by omega⟩) (valid k w)
def inputData (k w : Nat) : W k w w := inputs 2 (by omega)
def tailAddress (k w : Nat) : W k w k := add (head k w) (WordExpr.setWidth (count k w) k)
def flag (k w n : Nat) (b : E k w) : W k w n := mux b (literal 1) (literal 0)
def nextWord (k w : Nat) (j : Fin (entries k)) : W k w (bits k w) :=
  if j.val = 0 then mux (deq k w) (WordExpr.setWidth (add (head k w) (literal 1)) (bits k w)) (word k w j)
  else if j.val = 1 then WordExpr.setWidth
    (sub (add (count k w) (flag k w (k+1) (enq k w))) (flag k w (k+1) (deq k w))) (bits k w)
  else mux (.and (enq k w) (equal (tailAddress k w) (literal (BitVec.ofNat k (j.val-2)))))
    (WordExpr.setWidth (inputData k w) (bits k w)) (word k w j)

def resetKind (k : Nat) (j : Fin (entries k)) : ResetKind :=
  if j.val < 2 then .synchronous false else .hold

def outputBits (k w : Nat) : Vector (E k w) (w+2) := Vector.ofFn fun j =>
  if h : j.val = 0 then ready k w
  else if h : j.val = 1 then valid k w
  else (selectBalanced (head k w) (memory k w))[j.val-2]'(by omega)

def hardware (k w : Nat) : Circuit 0 (w+2) (entries k * bits k w) (w+2) :=
  wordBank s!"fifo_ring_d{2^k}_w{w}" (resetKind k) (nextWord k w) (outputBits k w)

def decode (s : Fin (entries k * bits k w) → Bool) : State w k :=
  ⟨fun a => (memory k w a.toFin).eval (fun _ => false) s,
    (head k w).eval (fun _ => false) s, (count k w).eval (fun _ => false) s⟩
def decodeInput (k w : Nat) (xs : Fin (w+2) → Bool) : Input (BitVec w) :=
  ⟨xs ⟨0,by omega⟩,(inputData k w).eval xs (fun _ => false),xs ⟨1,by omega⟩⟩

theorem word_inputs (k w : Nat) (j : Fin (entries k)) (s) (xs ys : Fin (w+2) → Bool) :
    (word k w j).eval xs s = (word k w j).eval ys s := bankWord_inputs j s xs ys
theorem head_inputs (k w : Nat) (s) (xs ys : Fin (w+2) → Bool) :
    (head k w).eval xs s = (head k w).eval ys s := by
  simp only [head,setWidth_correct]
  rw [word_inputs k w _ s xs ys]
theorem count_inputs (k w : Nat) (s) (xs ys : Fin (w+2) → Bool) :
    (count k w).eval xs s = (count k w).eval ys s := by
  simp only [count,setWidth_correct]
  rw [word_inputs k w _ s xs ys]
theorem memory_inputs (k w : Nat) (a : Fin (2^k)) (s) (xs ys : Fin (w+2) → Bool) :
    (memory k w a).eval xs s = (memory k w a).eval ys s := by
  simp only [memory,setWidth_correct]
  rw [word_inputs k w _ s xs ys]

theorem ready_correct (k w : Nat) (xs s) :
    (ready k w).eval xs s = decide ((decode s : State w k).count.toNat < 2^k) := by
  have hcap : 2^k < 2^(k+1) := by
    have := Nat.two_pow_pos k
    simp only [Nat.pow_succ,Nat.mul_two]
    omega
  simp only [ready,ult_correct,eval_literal,BitVec.ult_eq_decide,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hcap]
  rw [count_inputs k w s xs (fun _ => false)]
  rfl

theorem valid_correct (k w : Nat) (xs s) :
    (valid k w).eval xs s = ((decode s : State w k).count != 0) := by
  simp only [valid,Expr.eval,equal_correct,eval_literal]
  rw [count_inputs k w s xs (fun _ => false)]
  rfl

theorem enq_correct (k w : Nat) (xs s) :
    (enq k w).eval xs s = Circular.push (decode s) (decodeInput k w xs) := by
  simp [enq,Expr.eval,ready_correct,Circular.push,decodeInput]
theorem deq_correct (k w : Nat) (xs s) :
    (deq k w).eval xs s = Circular.pop (decode s) (decodeInput k w xs) := by
  simp [deq,Expr.eval,valid_correct,Circular.pop,decodeInput]

theorem word_next (k w : Nat) (j : Fin (entries k)) (s xs rst) :
    (word k w j).eval xs ((hardware k w).next s (xs,rst)) =
      if rst then if j.val < 2 then 0 else (word k w j).eval xs s
      else (nextWord k w j).eval xs s := by
  change (bankWord j).eval xs ((wordBank _ _ _ _).next s (xs,rst)) = _
  rw [wordBank_next]
  unfold resetKind
  by_cases hj : j.val < 2 <;> simp [hj,word]

theorem head_next (k w : Nat) (s xs rst) :
    (decode ((hardware k w).next s (xs,rst)) : State w k).head =
      ((machine w k).next (decode s) (decodeInput k w xs,rst)).head := by
  change (head k w).eval (fun _ => false) _ = _
  rw [head_inputs k w _ (fun _ => false) xs]
  simp only [head,setWidth_correct]
  rw [word_next]
  have hk : k ≤ bits k w := Nat.le_trans (Nat.le_succ k) (Nat.le_max_left _ _)
  cases rst <;> simp [nextWord,eval_mux,eval_literal,add_correct,
    machine,word_inputs k w _ s xs (fun _ => false),decode,head]
  rw [deq_correct]
  simp only [Circular.pop,decode]
  split <;> simp_all [BitVec.setWidth_setWidth_of_le _ hk]

theorem count_next (k w : Nat) (s xs rst) :
    (decode ((hardware k w).next s (xs,rst)) : State w k).count =
      ((machine w k).next (decode s) (decodeInput k w xs,rst)).count := by
  change (count k w).eval (fun _ => false) _ = _
  rw [count_inputs k w _ (fun _ => false) xs]
  simp only [count,setWidth_correct]
  rw [word_next]
  have hk : k+1 ≤ bits k w := Nat.le_max_left _ _
  cases rst <;> simp [nextWord,flag,eval_mux,eval_literal,add_correct,sub_correct,
    BitVec.setWidth_setWidth_of_le _ hk,machine,
    word_inputs k w _ s xs (fun _ => false),decode,count]
  simp [enq_correct,deq_correct,Circular.push,Circular.pop,decode,count]

theorem memory_next (k w : Nat) (s xs rst) (a : BitVec k) :
    (decode ((hardware k w).next s (xs,rst)) : State w k).buffer a =
      ((machine w k).next (decode s) (decodeInput k w xs,rst)).buffer a := by
  change (memory k w a.toFin).eval (fun _ => false) _ = _
  rw [memory_inputs k w _ _ (fun _ => false) xs]
  simp only [memory,setWidth_correct]
  rw [word_next]
  have hw : w ≤ bits k w := Nat.le_max_right _ _
  have h0 : 2+a.toNat ≠ 0 := by omega
  have h1 : 2+a.toNat ≠ 1 := by omega
  have h2 : ¬2+a.toNat < 2 := by omega
  have hdata : (inputData k w).eval xs s = (inputData k w).eval xs (fun _ => false) :=
    inputs_state _ _ _ _ _
  cases rst <;> simp [nextWord,h1,h2,eval_mux,eval_literal,setWidth_correct,equal_correct,
    tailAddress,add_correct,Expr.eval,machine,decode,decodeInput,
    word_inputs k w _ s xs (fun _ => false),enq_correct,Circular.push]
  · rw [head_inputs k w s xs (fun _ => false),count_inputs k w s xs (fun _ => false)]
    simp only [eq_comm]
    split <;> simp_all only [BitVec.setWidth_setWidth_of_le _ hw,BitVec.setWidth_eq,
      memory,setWidth_correct]
    all_goals rfl
  · simp only [memory,setWidth_correct]
    rfl

theorem decode_next (k w : Nat) (s xs rst) :
    (decode ((hardware k w).next s (xs,rst)) : State w k) =
      (machine w k).next (decode s) (decodeInput k w xs,rst) := by
  have hm := funext (memory_next k w s xs rst)
  cases hleft : decode ((hardware k w).next s (xs,rst))
  cases hright : (machine w k).next (decode s) (decodeInput k w xs,rst)
  have hh := head_next k w s xs rst
  have hcnt := count_next k w s xs rst
  simp only [hleft,hright] at hm hh hcnt
  cases hm; cases hh; cases hcnt
  rfl

/-- The physical ring inherits no-loss, no-overwrite and oldest-word behavior
from the universally quantified queue simulation invariant. -/
theorem hardware_preserves_queue (k w : Nat) (s xs) (g : Ghost) (history : Nat → BitVec w)
    (hs : g.Safe (2^k)) (hc : g.Controls (decode s)) (hm : g.Memory history (decode s)) :
    let input := decodeInput k w xs
    let g' := g.advance (Circular.push (decode s) input) (Circular.pop (decode s) input)
    g'.Safe (2^k) ∧ g'.Controls (decode ((hardware k w).next s (xs,false))) ∧
      g'.Memory (g.record history (decode s) input) (decode ((hardware k w).next s (xs,false))) ∧
      (Circular.pop (decode s) input = true → (decode s).buffer (decode s).head = history g.read) := by
  rw [decode_next]
  exact Circular.step_refines_queue hs hc hm

def readPayload (values : Fin (w+2) → Bool) : BitVec w :=
  (WordExpr.inputs 2 (by omega) : WordExpr 0 (w+2) 0 w).eval values Fin.elim0

def observe (values : Fin (w+2) → Bool) : Output (BitVec w) :=
  ⟨values ⟨0,by omega⟩,values ⟨1,by omega⟩,
    if values ⟨1,by omega⟩ then some (readPayload values) else none⟩

theorem output_ready (k w : Nat) (s xs) :
    (hardware k w).evalOutput s xs ⟨0,by omega⟩ = ((machine w k).out (decode s)).enqReady := by
  simp [Circuit.evalOutput,hardware,wordBank,outputBits,ready_correct,machine]

theorem output_valid (k w : Nat) (s xs) :
    (hardware k w).evalOutput s xs ⟨1,by omega⟩ = ((machine w k).out (decode s)).deqValid := by
  simp [Circuit.evalOutput,hardware,wordBank,outputBits,valid_correct,machine]

theorem output_data (k w : Nat) (s xs) :
    readPayload ((hardware k w).evalOutput s xs) = (decode s : State w k).buffer (decode s).head := by
  unfold readPayload
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [eval_bit _ _ _ j hj]
  simp only [inputs,Vector.getElem_ofFn,Expr.eval,Circuit.evalOutput,hardware,wordBank,Fin.getElem_fin,
    outputBits,Vector.getElem_ofFn]
  have h0 : 2+j ≠ 0 := by omega
  have h1 : 2+j ≠ 1 := by omega
  simp only [h0,h1,↓reduceDIte,Nat.add_sub_cancel_left]
  rw [←eval_bit (selectBalanced (head k w) (memory k w)) xs s j hj,selectBalanced_correct]
  rw [head_inputs k w s xs (fun _ => false),memory_inputs k w _ s xs (fun _ => false)]
  rfl

theorem decode_output (k w : Nat) (s xs) :
    observe ((hardware k w).evalOutput s xs) = (machine w k).out (decode s) := by
  simp only [observe,output_ready,output_valid,output_data,machine]

theorem hardware_moore (k w : Nat) : (hardware k w).IsMoore := by
  intro s a b
  funext j
  simp only [Circuit.evalOutput,hardware,wordBank,outputBits,Fin.getElem_fin,Vector.getElem_ofFn]
  split
  · simp only [ready_correct]
  · split
    · simp only [valid_correct]
    · rename_i h0 h1
      have hj : j.val-2 < w := by have := j.isLt; omega
      rw [←eval_bit (selectBalanced (head k w) (memory k w)) a s (j.val-2) hj,
        ←eval_bit (selectBalanced (head k w) (memory k w)) b s (j.val-2) hj,
        selectBalanced_correct,selectBalanced_correct,head_inputs k w s a b,
        memory_inputs k w _ s a b]

theorem hardware_state (k w : Nat) (s₀) (xs : Nat → (Fin (w+2) → Bool) × Bool) (t : Nat) :
    decode (((hardware k w).denote (hardware_moore k w)).stateFrom s₀ xs t) =
      (machine w k).stateFrom (decode s₀) (fun n => (decodeInput k w (xs n).1,(xs n).2)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [PMachine.stateFrom_succ]
    change decode ((hardware k w).next _ (xs t)) = _
    rw [decode_next,ih]

theorem storage_bits (k w : Nat) : (hardware k w).ffBits = (2+2^k)*max (k+1) w := rfl

end HDLean.Fifo.Circular.Physical
