import Designs.Fifo.Spec
import HDLean.Verification.Simulation
namespace HDLean.Fifo.Circular

/-- Power-of-two ring with unreset RAM and modular pointers. -/
structure State (w k : Nat) where
  buffer : BitVec k → BitVec w
  head : BitVec k
  count : BitVec (k + 1)

/-- Executable circular-buffer model. Its general refinement proof is a separate obligation. -/
def machine (w k : Nat) : PMachine (State w k) (Input (BitVec w) × Bool) (Output (BitVec w)) where
  out s := ⟨decide (s.count.toNat < 2 ^ k), s.count != 0,
    if s.count != 0 then some (s.buffer s.head) else none⟩
  next s x :=
    if x.2 then { s with head := 0, count := 0 }
    else
      let enq := x.1.enqValid && decide (s.count.toNat < 2 ^ k)
      let deq := x.1.deqReady && s.count != 0
      let tail := s.head + s.count.setWidth k
      { buffer := fun j => if enq && j == tail then x.1.enqData else s.buffer j
        head := if deq then s.head + 1 else s.head
        count := s.count + (if enq then 1 else 0) - (if deq then 1 else 0) }

def check (w k cycles seed : Nat) : Except String Unit := do
  let mut seed := seed
  let mut s : State w k := ⟨fun a => BitVec.ofNat w (seed + a.toNat * 31),
    BitVec.ofNat k seed, BitVec.ofNat (k + 1) seed⟩
  let mut q : List (BitVec w) := []
  let m := machine w k
  for t in [:cycles] do
    seed := Verification.random seed
    let i : Input (BitVec w) := ⟨seed / 4 % 2 == 1, BitVec.ofNat w (seed / 256), seed / 16 % 2 == 1⟩
    let rst := t == 0 || t % 97 == 0
    if t > 0 && m.out s != (spec (BitVec w) (2 ^ k)).out q then
      throw s!"circular FIFO mismatch k={k}, w={w}, cycle={t}"
    s := m.next s (i, rst)
    q := if rst then [] else (spec (BitVec w) (2 ^ k)).next q i
end HDLean.Fifo.Circular
