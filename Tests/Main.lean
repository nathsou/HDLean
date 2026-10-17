import HDLean
import Designs
import Tests.Backend
open HDLean HDLean.Verification HDLean.Rtl

/-!
Simulation regressions. The proofs cover every design; these runs guard the
compiled code that evaluates designs, bit-blasts them and emits them, and they
exercise the specifications on concrete traces.
-/

private def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

private def require (p : Bool) (message : String) : IO Unit :=
  unless p do throw (IO.userError message)

private def draw (seed : Nat) : Nat := random seed

/-- Random FIFO input words: valid, ready, data. -/
private def fifoInputs (w seed : Nat) : Array Nat × Nat :=
  let s1 := draw seed; let s2 := draw s1; let s3 := draw s2
  (#[s1 / 65536 % 2, s2 / 65536 % 2, s3 % 2 ^ w], s3)

/-- A single-clock design against a reference machine through an observation,
from the all-zero store, with a reset at cycle 0 and then now and then (the
reference restarts with it). -/
private def checkAgainst {σ ο : Type} [BEq ο] [Repr ο] (name : String) (d : Design) (m : Machine σ (Array Nat) ο)
    (obs : Array Nat → ο) (inputs : Nat → Array Nat × Nat) (cycles seed : Nat) : IO Unit := do
  let mut st : Store := default
  let mut q := m.init
  let mut seed := seed
  st := d.step st (#[], true)
  for t in [:cycles] do
    let (ins, seed') := inputs seed
    seed := seed'
    let actual := obs (d.output st ins)
    require (actual == m.out q) s!"{name}: mismatch at cycle {t}: design {repr actual}, reference {repr (m.out q)}"
    let rst := seed % 37 == 0
    st := d.step st (ins, rst)
    q := if rst then m.init else m.next q ins

instance : Repr (Fifo.Output (BitVec w)) := ⟨fun o _ => s!"⟨{o.enqReady}, {o.deqValid}, {(o.deqData.map (·.toNat))}⟩"⟩

private def checkPipeline (w cycles seed : Nat) : IO Unit := do
  let d := SkidBuffer.Word.design w
  let m := SkidBuffer.Word.wordSpec w
  let mut st : Store := d.step default (#[], true)
  let mut q := m.init
  let mut seed := seed
  for t in [:cycles] do
    let (ins, seed') := fifoInputs w seed
    seed := seed'
    let outs := d.output st ins
    for j in List.finRange 3 do
      require (SkidBuffer.Word.observe w outs j == m.out q j) s!"pipeline w={w}: mismatch at cycle {t}, stage {j.val}"
    st := d.step st (ins, false)
    -- Force the next queues: the network's state is a function of the stage.
    let snapshot := Vector.ofFn (m.next q ins)
    q := fun j => snapshot[j]

/-- The word-level CPU's retirement reports against the ISA, on the sum program. -/
private def checkToy16 (cycles : Nat) : IO Unit := do
  let imem := Toy16.sumProgram
  let mut st : Store := default
  let mut n := 0
  for t in [:cycles] do
    let r := Toy16.Word.observe (Bundle.decode Toy16.Word.CpuOut
      ((Toy16.Word.design.output st (Toy16.Word.fetch imem st)).getD · 0))
    if t > 0 then
      if let some r := r then
        let e := Toy16.isaRetire imem (Toy16.ArchState.atReset (fun _ => 0) (fun _ => 0)) n
        require (r.pc == e.pc && r.instr == e.instr && r.halt == e.halt) s!"toy16: retirement {n} differs at cycle {t}"
        n := n + 1
    st := Toy16.Word.design.step st (Toy16.Word.fetch imem st, t == 0)
  require (n ≥ 20) s!"toy16: only {n} retirements in {cycles} cycles"

/-- The dual-clock design against the dual-clock model, from a state the model
decodes, under random edges, resets, inputs and sampling masks. -/
private def checkAsync (k w cycles seed : Nat) : IO Unit := do
  let md := AsyncFifo.Word.design k w
  let mut s : MDesign.State := ⟨#[default, default], #[0, 0], #[0, 0], #[#[]]⟩
  let mut m := AsyncFifo.Word.decode (k := k) (w := w) s
  let mut seed := seed
  for t in [:cycles] do
    let s1 := draw seed; let s2 := draw s1; let s3 := draw s2; let s4 := draw s3
    seed := s4
    let i : AsyncFifo.Input k w := ⟨s1 % 3 != 0, s1 / 3 % 3 != 0, t < 3 || s2 % 41 == 0, t < 3 || s2 / 41 % 43 == 0,
      s3 % 2 == 1, BitVec.ofNat w (s3 / 2), s3 / 7 % 2 == 1, BitVec.ofNat (k + 1) s4, BitVec.ofNat (k + 1) (s4 / 64)⟩
    if t ≥ 3 then
      require (AsyncFifo.Word.observe w md s == AsyncFifo.observe m) s!"async k={k} w={w}: ports differ at step {t}"
    s := md.next s (AsyncFifo.Word.event i)
    m := AsyncFifo.next m i
    let d := AsyncFifo.Word.decode (k := k) (w := w) s
    let sameMem := (List.range (2 ^ k)).all fun a => d.memory (BitVec.ofNat k a) == m.memory (BitVec.ofNat k a)
    require (d.write == m.write && d.read == m.read && d.seenWrite == m.seenWrite && d.seenRead == m.seenRead &&
      sameMem) s!"async k={k} w={w}: state differs at step {t}"

def main : IO Unit := do
  HDLean.Tests.checkBackendTexts
  say "PASS: emitted SV/AIGER/RTLIL decode back to the lowered graph; changed files rejected."
  HDLean.Tests.checkWordPass
  say "PASS: the word-level pass rewrites a redundant module, which still checks and computes the same."
  for seed in [1, 42, 999] do
    checkAgainst "counter" Counter.Word.design Counter.Word.wordSpec Counter.Word.value
      (fun s => let s' := draw s; (#[s' / 65536 % 2], s')) 300 seed
  for w in [1, 8, 16] do
    for seed in [1, 42, 999] do
      checkAgainst s!"fifo w={w}" (Fifo.Word.design w) (Fifo.Word.queueSpec 2 w) (Fifo.Word.observe w)
        (fifoInputs w) 300 seed
      checkPipeline w 300 seed
      for k in [1, 2, 4] do
        checkAgainst s!"ring k={k} w={w}" (Fifo.Circular.Word.design k w) (Fifo.Word.queueSpec (2 ^ k) w)
          (Fifo.Word.observe w) (fifoInputs w) 300 seed
  say "PASS: 900 counter, 2,700 FIFO, 2,700 pipeline and 8,100 general-depth FIFO cycles against the references."
  checkToy16 60
  say "PASS: the word-level CPU retires the sum program as the ISA does."
  for k in [1, 2, 4] do
    for w in [1, 8] do
      for seed in [1, 42, 999] do checkAsync k w 400 seed
  say "PASS: 7,200 dual-clock steps: the multi-clock design is the dual-clock model, ports included."
  for d in ["counter", "fifo", "pipeline", "ring", "ram"] do
    let design := match d with
      | "counter" => Counter.Word.design | "fifo" => Fifo.Word.design 8 | "pipeline" => SkidBuffer.Word.design 8
      | "ring" => Fifo.Circular.Word.design 4 8 | _ => RAM.Word.design 4 8
    match design.optimized.toDag with
    | none => throw (IO.userError s!"{d} does not bit-blast")
    | some g => for seed in [1, 42] do
        match checkDag g 150 seed with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"{d}: {e}")
  say "PASS: bit-blasted graphs of five designs against their lowered gate graphs."
  for k in [0, 1, 2, 3, 4] do
    for seed in [1, 42, 999] do
      match Fifo.Circular.check 8 k 500 seed with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
      match AsyncFifo.check k 8 1000 seed with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
  say "PASS: 7,500 circular-buffer model cycles; 15,000 dual-clock model steps."
