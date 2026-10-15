import HDLean.Semantics.Clock
import HDLean.Verification.Simulation
namespace HDLean.AsyncFifo

/-- Decode Gray pointers; a finite xor network, not a mathematical oracle. -/
def ungray (g : BitVec w) : BitVec w :=
  (List.range w).foldl (fun acc j => acc ^^^ (g >>> j)) 0

/-- Dual-clock FIFO state. Pointer synchronizers and memory all power up arbitrarily. -/
structure State (k w : Nat) where
  memory : BitVec k → BitVec w
  write : BitVec (k + 1)
  read : BitVec (k + 1)
  seenWrite : Sync2 (BitVec (k + 1))
  seenRead : Sync2 (BitVec (k + 1))

/-- Edges, resets, and metastability masks are explicit independent environmental inputs. -/
structure Input (k w : Nat) where
  writeEdge : Bool
  readEdge : Bool
  writeReset : Bool
  readReset : Bool
  valid : Bool
  data : BitVec w
  ready : Bool
  writeMask : BitVec (k + 1)
  readMask : BitVec (k + 1)

/-- Current ready/valid ports; delayed pointers may conservatively suppress transfers. -/
def enqReady (s : State k w) : Bool :=
  s.write != (ungray s.seenRead.second ^^^ BitVec.ofNat (k + 1) (2 ^ k))
def deqValid (s : State k w) : Bool := s.read != ungray s.seenWrite.second

def push (s : State k w) (i : Input k w) : Bool := i.writeEdge && !i.writeReset && i.valid && enqReady s
def pop (s : State k w) (i : Input k w) : Bool := i.readEdge && !i.readReset && i.ready && deqValid s

/-- Read data is sampled before the global step; concurrent writes cannot change the sampled word. -/
def data (s : State k w) : BitVec w := s.memory (s.read.setWidth k)

/-- Independent edges update only the associated domain. Synchronizer flops sample old first stages. -/
def next (s : State k w) (i : Input k w) : State k w :=
  let wp := if i.writeEdge && i.writeReset then 0 else if push s i then s.write + 1 else s.write
  let rp := if i.readEdge && i.readReset then 0 else if pop s i then s.read + 1 else s.read
  { memory := fun a => if push s i && a == s.write.setWidth k then i.data else s.memory a
    write := wp
    read := rp
    seenWrite := if i.readEdge then
      if i.readReset then ⟨0, 0⟩ else ⟨sampleBits (gray s.write) (gray wp) i.readMask, s.seenWrite.first⟩
      else s.seenWrite
    seenRead := if i.writeEdge then
      if i.writeReset then ⟨0, 0⟩ else ⟨sampleBits (gray s.read) (gray rp) i.writeMask, s.seenRead.first⟩
      else s.seenRead }

/-- No edges means no physical state changes, including memory. -/
theorem no_edges (s : State k w) (i : Input k w) (hw : i.writeEdge = false) (hr : i.readEdge = false) :
    next s i = s := by
  cases s
  simp [next, push, pop, hw, hr]

/-- Simultaneous reset edges establish empty control without resetting memory. -/
theorem reset_empty (s : State k w) (i : Input k w)
    (hw : i.writeEdge = true) (hr : i.readEdge = true)
    (hwr : i.writeReset = true) (hrr : i.readReset = true) :
    (next s i).write = 0 ∧ (next s i).read = 0 ∧ (next s i).memory = s.memory := by
  simp [next, push, hw, hr, hwr, hrr]

/-- The executable regression varies edge interleavings and every per-bit sampling mask. -/
def check (k w cycles seed : Nat) : Except String Unit := do
  let mut seed := seed
  let mut s : State k w := ⟨fun a => BitVec.ofNat w (a.toNat * 17 + seed), 0, 0, ⟨0,0⟩, ⟨0,0⟩⟩
  let mut queue : List (BitVec w) := []
  for t in [:cycles] do
    seed := Verification.random seed
    let i : Input k w := ⟨seed % 2 == 1, seed / 2 % 2 == 1, false, false,
      seed / 4 % 2 == 1, BitVec.ofNat w (seed / 256), seed / 8 % 2 == 1,
      BitVec.ofNat (k + 1) (seed / 16), BitVec.ofNat (k + 1) (seed / 128)⟩
    let enq := push s i
    let deq := pop s i
    if deq then
      match queue with
      | [] => throw s!"async underflow at step {t}"
      | a :: tail =>
        if data s != a then throw s!"async reordering at step {t}"
        queue := tail
    if enq then queue := queue ++ [i.data]
    if queue.length > 2 ^ k then throw s!"async overflow at step {t}"
    s := next s i
end HDLean.AsyncFifo
