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

/-- A stage: valid, amount, count, read address of its delay line, and the
two words behind the count (for the 1p and 2p stages `h` is a flag). -/
hdl_record Stage where
  v : 1 := 0
  i : 8
  y : W
  ra : 8
  h : W
  g : W

hdl_record Glob where
  gen : 8 := 0
  done : 1 := 0
  answer : W := 0
  fin : 1 := 0

abbrev State := Both (Lanes "s" stages Stage) Glob

/-- Delay lines for the coins above 2p (stages 2 … 7). -/
def mems : Array MemSpec := ((List.range (stages - 2)).map fun s => ms s!"hist{s + 2}" 8 W).toArray

def ctx : Ctx := solverCtx "euler31" W State
  ⟨Lanes.ofFn fun s => { Stage.resets with h := if coins[s]! ≤ 2 then .sync 0 else .none }, Glob.resets⟩ mems

def body : M ctx Wiring := solver "P031" State fun ⟨sts, g⟩ => do
  -- the generator: amounts 0 … 200, a single way to make 0
  let running ← not1 (← geK g.gen (target + 1))
  let gen' ← ite' running (← addK g.gen 1) g.gen
  let x0 ← zx (← eqK g.gen 0) W
  let mut vin := running
  let mut iin := g.gen
  let mut xin := x0
  let mut next : Array (Stage Sig) := #[]
  let mut writes : Array (Array WritePort) := #[]
  let mut lastY := x0
  let mut finNext := running
  for (st, s) in sts.lanes.zipIdx do
    let c := coins[s]!
    -- this stage at this cycle sees (vin, iin, xin) from the previous stage and
    -- needs its own output for amount iin − c (zero below c)
    let zero ← lit W 0
    if c ≤ 2 then
      -- from the output register (c = 1) or the one before it (c = 2, kept in
      -- g); h is a flag, registered a cycle ahead: iin ≥ c
      let prev := if c == 1 then st.y else st.g
      let back ← ite' (← bit st.h 0) prev zero
      let yNew ← add xin back
      let has' ← zx (← and1 vin (← geK iin (c - 1))) W
      next := next.push { st with v := vin, i := iin, y := yNew, h := has', g := st.y }
    else
      -- from the block RAM delay line: written from the output registers, read
      -- two cycles ahead (into the RAM's own output register h, then g)
      let yNew ← add xin st.g
      writes := writes.push #[port st.v st.i st.y]
      let h ← memRead (s - 2) W st.ra
      let g' ← ite' (← and1 vin (← geK iin (c - 1))) st.h zero
      let raNext ← subK (← addK iin 3) c
      next := next.push { v := vin, i := iin, y := yNew, ra := raNext, h, g := g' }
    if s + 1 == stages then
      -- the last stage takes amount 200 this cycle: its output is the answer next cycle
      finNext ← and1 vin (← eqK iin target)
    lastY := st.y
    vin := st.v
    iin := st.i
    xin := st.y
  -- the last stage's output registers hold ways[i] for all coins
  let answer' ← ite' g.fin lastY g.answer
  let done' ← or1 g.done g.fin
  finish g.done g.answer
    ⟨Lanes.ofFn fun s => next.getD s default, { gen := gen', done := done', answer := answer', fin := finNext }⟩ writes

def design : Except String Design := solverDesign ctx body

def problem : Problem :=
  { number := 31, title := "Coin sums",
    idea := "A systolic pipeline with one stage per coin; amounts stream through, each stage adding its own output from c amounts earlier, kept in a block RAM delay line.",
    answerWidth := W, design, reference, maxCycles := 1000 }

end HDLean.Euler.P031
