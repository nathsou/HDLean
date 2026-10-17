import Designs.Euler.Kit

/-!
# Problem 31: coin sums

The number of ways to make £2 from the coins 1p, 2p, 5p, 10p, 20p, 50p, £1, £2.

The classic dynamic programme `ways[i] += ways[i − c]`, one coin after another,
as a systolic pipeline: one stage per coin, the amounts `i = 0 … 200` streamed
through the stages one per cycle. Stage `c` adds to each incoming count its own
output from `c` amounts earlier: a register for the 1p and 2p coins, a block
RAM delay line for the others (written from the stage's output register, read
two cycles ahead so that the RAM's output never feeds an adder directly). All eight coins are applied
in one pass: the answer leaves the last stage 209 cycles after reset.
-/
namespace HDLean.Euler.P031
open HDLean.Rtl HDLean.Rtl.Build

def coins : List Nat := [1, 2, 5, 10, 20, 50, 100, 200]
def target : Nat := 200
def W : Nat := 17

def reference (_ : Unit) : Nat := Id.run do
  let mut ways := (Array.range (target + 1)).map fun i => if i == 0 then 1 else 0
  for c in coins do
    for i in [c:target + 1] do
      ways := ways.set! i (ways[i]! + ways[i - c]!)
  return ways[target]!

def stages : Nat := coins.length

/-- Per stage: valid, amount, count, read address of its delay line; then the
generator and the result. -/
def regs : Array RegSpec :=
  ((List.range stages).flatMap fun s =>
    -- for the 1p and 2p stages, h is a flag and must start cleared
    [rs s!"v{s}" 1 (.sync 0), rs s!"i{s}" 8, rs s!"y{s}" W, rs s!"ra{s}" 8,
     rs s!"h{s}" W (if coins[s]! ≤ 2 then .sync 0 else .none), rs s!"g{s}" W]).toArray ++
  #[rs "gen" 8 (.sync 0), rs "done" 1 (.sync 0), rs "answer" W (.sync 0), rs "fin" 1 (.sync 0)]

/-- Delay lines for the coins above 2p (stages 2 … 7). -/
def mems : Array MemSpec := ((List.range (stages - 2)).map fun s => ms s!"hist{s + 2}" 8 W).toArray

def ctx : Ctx := solverCtx "euler31" W regs mems

def base (s : Nat) : Nat := 6 * s
def genIdx : Nat := 6 * stages

def body : M ctx Wiring := do
  let gen ← rd genIdx 8
  let done ← rd (genIdx + 1) 1
  let answer ← rd (genIdx + 2) W
  let fin ← rd (genIdx + 3) 1
  -- the generator: amounts 0 … 200, a single way to make 0
  let running ← not1 (← geK gen (target + 1))
  let gen' ← ite' running (← addK gen 1) gen
  let x0 ← zx (← eqK gen 0) W
  let mut vin := running
  let mut iin := gen
  let mut xin := x0
  let mut nexts : Array Nat := #[]
  let mut writes : Array (Array WritePort) := #[]
  let mut lastV := running
  let mut lastI := gen
  let mut lastY := x0
  let mut finNext := running
  for s in [0:stages] do
    let c := coins[s]!
    let v ← rd (base s) 1
    let i ← rd (base s + 1) 8
    let y ← rd (base s + 2) W
    let ra ← rd (base s + 3) 8
    let h1 ← rd (base s + 4) W
    let h2 ← rd (base s + 5) W
    -- this stage at this cycle sees (vin, iin, xin) from the previous stage and
    -- needs its own output for amount iin − c (zero below c)
    let zero ← lit W 0
    if c ≤ 2 then
      -- from the output register (c = 1) or the one before it (c = 2, kept in
      -- h2); h1 is a flag, registered a cycle ahead: iin ≥ c
      let prev := if c == 1 then y else h2
      let has ← bit h1 0
      let back ← ite' has prev zero
      let yNew ← add xin back
      let has' ← zx (← and1 vin (← geK iin (c - 1))) W
      nexts := nexts ++ #[vin.ref, iin.ref, yNew.ref, ra.ref, has'.ref, y.ref]
    else
      -- from the block RAM delay line: written from the output registers, read
      -- two cycles ahead (into the RAM's own output register h1, then h2)
      let yNew ← add xin h2
      writes := writes.push #[port v i y]
      let h ← memRead (s - 2) W ra
      let h2' ← ite' (← and1 vin (← geK iin (c - 1))) h1 zero
      let raNext ← subK (← addK iin 3) c
      nexts := nexts ++ #[vin.ref, iin.ref, yNew.ref, raNext.ref, h.ref, h2'.ref]
    if s + 1 == stages then
      -- the last stage takes amount 200 this cycle: its output is the answer next cycle
      finNext ← and1 vin (← eqK iin target)
    lastV := v
    lastI := i
    lastY := y
    vin := v
    iin := i
    xin := y
  -- the last stage's output registers hold ways[i] for all coins
  let _ := lastV
  let _ := lastI
  let answer' ← ite' fin lastY answer
  let done' ← or1 done fin
  pure (solverWiring ⟨done, answer.ref, nexts ++ #[gen'.ref, done'.ref, answer'.ref, finNext.ref], writes⟩)

def design : Design := single ctx body

def problem : Problem :=
  { number := 31, title := "Coin sums",
    idea := "A systolic pipeline with one stage per coin; amounts stream through, each stage adding its own output from c amounts earlier, kept in a block RAM delay line.",
    answerWidth := W, design, reference, maxCycles := 1000 }

end HDLean.Euler.P031
