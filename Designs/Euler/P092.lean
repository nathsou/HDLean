import Designs.Euler.Kit

/-!
# Problem 92: square digit chains

How many starting numbers below ten million arrive at 89?

A number's chain depends only on the sum `s` of the squares of its digits, and
`s ≤ 7·81 = 567`. So instead of ten million chains:

* a counting programme computes `c[s]`, the number of 7-digit strings (leading
  zeros allowed) with digit-square sum `s`: seven rounds of the convolution
  `c'[s] = Σ_d c[s − d²]`, streamed **two values of `s` per cycle** through a
  delay line with ten taps for each and two pipelined adder trees, ping-ponging
  between block RAM banks split by parity;
* meanwhile a chain engine classifies every `s < 200` (does it reach 89?) into a
  one-bit table indexed by `s` in BCD, memoised: a chain stops as soon as it falls
  below its start;
* the last round adds up the `c[s]` whose `s` reaches 89: below 200 straight from
  the table, above it through `f(s) < 200` (the digit-square sum of `s`, at most
  178 there), computed from a BCD counter of the stream.
-/
namespace HDLean.Euler.P092
open HDLean.Rtl HDLean.Rtl.Build

def W : Nat := 24
def rounds : Nat := 7
def taps : List Nat := (List.range 10).map (· ^ 2)
def maxS : Nat := 81 * rounds

def digitSq (n : Nat) : Nat := Id.run do
  let mut n := n
  let mut s := 0
  for _ in [:8] do
    s := s + (n % 10) ^ 2
    n := n / 10
  return s

def reaches89 (n : Nat) : Bool := Id.run do
  let mut v := n
  for _ in [:100] do
    if v == 1 then return false
    if v == 89 then return true
    v := digitSq v
  return false

def reference (_ : Unit) : Nat := Id.run do
  let mut c := (Array.range (maxS + 1)).map fun s => if s == 0 then 1 else 0
  for _ in [:rounds] do
    c := (Array.range (maxS + 1)).map fun s => taps.foldl (fun acc t => if t ≤ s then acc + c[s - t]! else acc) 0
  let mut total := 0
  for s in [1:maxS + 1] do
    if reaches89 s then total := total + c[s]!
  return total

/-! ## Registers -/

def classLimit : Nat := 200
def LINE : Nat := 83        -- delay line: x[2m+1], x[2m], x[2m−1], …
def AWB : Nat := 9          -- bank addresses: pair indices

/-- DP control: round, input pair, mode (0 stream, 1 drain, 2 wait), drain
counter, the round's last pair and the input limit 81·rnd; the last round: BCD of
2m at level 2, the class table addresses (level 3), classes (level 4), the masked
pair sum (level 5); the classifier (values in BCD). -/
hdl_record Ctl where
  rnd : 3 := 0
  m : AWB := 0
  mode : 2 := 0
  drain : 3 := 0
  mend : AWB := ((81 + 3) / 2)
  lim : 10 := 0
  sb : 12 := 0
  ah : 12
  al : 12
  ch : 1
  cl : 1
  ps : W
  pv : 1 := 0
  acc : W := 0
  done : 1 := 0
  answer : W := 0
  cs : 12 := 1
  part : 12
  cv : 12 := 1
  sqh : 8
  phase : 1 := 0
  cdone : 1 := 0

/-- Pipeline levels 0 … 4 (taps, l1, l2, l3, l4): valid and pair index. -/
hdl_record Pipe where
  v : 1 := 0
  pm : AWB

/-- An adder tree over ten taps: five, three, two and one partial sums. -/
hdl_record Tree where
  a0 : W
  a1 : W
  a2 : W
  a3 : W
  a4 : W
  b0 : W
  b1 : W
  b2 : W
  c0 : W
  c1 : W
  d : W

/-- Control, the pipeline, the two adder trees (hi: s = 2m+1, lo: s = 2m) and
the delay line. -/
abbrev State := Both Ctl (Both (Lanes "p" 5 Pipe) (Both (Lanes "t" 2 Tree) (Lanes "d" LINE (Word W))))

/-- Banks: even and odd `s`, for rounds of each parity; three copies of the class
table (classifier, hi lookup, lo lookup), indexed by BCD. -/
def mems : Array MemSpec := #[ms "be0" AWB W, ms "bo0" AWB W, ms "be1" AWB W, ms "bo1" AWB W,
  ms "classA" 12 1, ms "classH" 12 1, ms "classL" 12 1]

def ctx : Ctx := solverCtx "euler92" W State
  ⟨Ctl.resets, Lanes.replicate Pipe.resets, Lanes.replicate (Bundle.fill Tree .none), Lanes.replicate ⟨.sync 0⟩⟩ mems

/-- Increment a 3-digit BCD number. -/
def bcdInc (x : Sig 12) : M ctx (Sig 12) := do
  let o ← slice x 0 4
  let t ← slice x 4 4
  let h ← slice x 8 4
  let o9 ← eqK o 9
  let t9 ← eqK t 9
  let o' ← ite' o9 (← lit 4 0) (← addK o 1)
  let t' ← ite' o9 (← ite' t9 (← lit 4 0) (← addK t 1)) t
  let h' ← ite' (← and1 o9 t9) (← addK h 1) h
  concat h' (← concat t' o')

/-- Add two 3-digit BCD numbers (no overflow past 999 here). -/
def bcdAdd (a b : Sig 12) : M ctx (Sig 12) := do
  -- carry select: every digit computes its sum for both carries in parallel,
  -- then the carries ripple through two levels of multiplexers
  let mut carry ← lit 1 0
  let mut digits : List (Sig 4) := []
  for i in [0:3] do
    let x ← zx (← slice a (4 * i) 4) 5
    let y ← zx (← slice b (4 * i) 4) 5
    let s0 ← add x y
    let s1 ← addK s0 1
    let over0 ← geK s0 10
    let over1 ← geK s0 9
    let d0 ← slice (← ite' over0 (← subK s0 10) s0) 0 4
    let d1 ← slice (← ite' over1 (← subK s0 9) s1) 0 4
    digits := digits ++ [← ite' carry d1 d0]
    carry ← ite' carry over1 over0
  concat digits[2]! (← concat digits[1]! digits[0]!)

/-- The square of a decimal digit, in BCD. -/
def sq (d : Sig 4) : M ctx (Sig 8) := do
  let mut r ← lit 8 0
  for k in [1:10] do
    let v := (k * k / 10) * 16 + k * k % 10
    r ← ite' (← eqK d k) (← lit 8 v) r
  pure r

set_option maxRecDepth 20000 in
def body : M ctx Wiring := solver "P092" State fun ⟨g, pipe, trees, lineR⟩ => do
  let rnd := g.rnd
  let m := g.m
  let mode := g.mode
  let drain := g.drain
  let mend := g.mend
  let lim := g.lim
  let vs := pipe.lanes.map (·.v)
  let pms := pipe.lanes.map (·.pm)
  let tree (t : Tree Sig) : List (Sig W) × List (Sig W) × List (Sig W) × Sig W :=
    ([t.a0, t.a1, t.a2, t.a3, t.a4], [t.b0, t.b1, t.b2], [t.c0, t.c1], t.d)
  let (h1, h2, h3, _) := tree (trees.getD 0 default)
  let (l1, l2, l3, l4) := tree (trees.getD 1 default)
  let h4 := (trees.getD 0 default).d
  let sb := g.sb
  let ah := g.ah
  let al := g.al
  let ch := g.ch
  let cl := g.cl
  let ps := g.ps
  let pv := g.pv
  let acc := g.acc
  let done := g.done
  let answer := g.answer
  let cs := g.cs
  let part := g.part
  let cv := g.cv
  let sqh := g.sqh
  let phase := g.phase
  let cdone := g.cdone
  let line := lineR.lanes.map (·.v)
  -- the classifier: one chain step per two cycles (test and two squares, then
  -- the third square), in BCD; the class table is memoised
  let cv1 ← eqK cv 1
  let cv89 ← eqK cv 0x89
  let below ← ult cv cs
  let known ← readMem "classA" 1 cv
  let finishS ← or1 cv1 (← or1 cv89 below)
  let clsVal ← ite' cv1 (← lit 1 0) (← ite' cv89 (← lit 1 1) known)
  let classifying ← not1 cdone
  let ph0 ← and1 classifying (← not1 phase)
  let ph1 ← and1 classifying phase
  let writeCls ← and1 ph0 finishS
  let csLast ← eqK cs 0x199
  let csNext ← bcdInc cs
  let cs' ← ite' writeCls csNext cs
  let part' ← zx (← bcdAdd (← zx (← sq (← slice cv 0 4)) 12) (← zx (← sq (← slice cv 4 4)) 12)) 12
  let sqh' ← sq (← slice cv 8 4)
  let full ← bcdAdd part (← zx sqh 12)
  let cv' ← ite' writeCls csNext (← ite' ph1 full cv)
  let step ← and1 ph0 (← not1 finishS)
  let phase' ← ite' step (← lit 1 1) (← lit 1 0)
  let cdone' ← or1 cdone (← and1 writeCls csLast)
  -- the DP stream: pair m carries x[2m] and x[2m+1]
  let isStream ← eqK mode 0
  let isDrain ← eqK mode 1
  let isWait ← eqK mode 2
  let running ← ltK rnd rounds
  let streaming ← and1 running isStream
  let parity ← bit rnd 0
  -- round r reads the banks written by round r − 1 (parity of r − 1)
  let e0 ← readMem "be0" W m
  let o0 ← readMem "bo0" W m
  let e1 ← readMem "be1" W m
  let o1 ← readMem "bo1" W m
  let ev ← ite' parity e0 e1
  let od ← ite' parity o0 o1
  let rnd0 ← eqK rnd 0
  let zero ← lit W 0
  let sEven ← shlK (← zx m 10) 1
  let sOdd ← addK sEven 1
  let inE ← not1 (← ult lim sEven)
  let inO ← not1 (← ult lim sOdd)
  let m0 ← eqK m 0
  let xE ← ite' rnd0 (← zx m0 W) (← ite' inE ev zero)
  let xO ← ite' rnd0 zero (← ite' inO od zero)
  let xEIn ← ite' streaming xE zero
  let xOIn ← ite' streaming xO zero
  let atEnd ← eq m mend
  let m' ← ite' streaming (← ite' atEnd (← lit AWB 0) (← addK m 1)) m
  -- the delay line shifts by two: newest x[2m+1], then x[2m]
  let line' := xOIn :: xEIn :: line.take (LINE - 2)
  -- adder trees: hi (s = 2m+1) over line[t], lo (s = 2m) over line[t + 1]
  let mkTree (off : Nat) (q1 : List (Sig W)) (q2 : List (Sig W)) (q3 : List (Sig W)) :
      M ctx (List (Sig W) × List (Sig W) × List (Sig W) × Sig W) := do
    let tapVals := taps.map fun t => line[t + off]!
    let n1 ← (List.range 5).mapM fun k => add tapVals[2 * k]! tapVals[2 * k + 1]!
    let n2 := [← add q1[0]! q1[1]!, ← add q1[2]! q1[3]!, q1[4]!]
    let n3 := [← add q2[0]! q2[1]!, q2[2]!]
    let n4 ← add q3[0]! q3[1]!
    pure (n1, n2, n3, n4)
  let (h1', h2', h3', h4') ← mkTree 0 h1 h2 h3
  let (l1', l2', l3', l4') ← mkTree 1 l1 l2 l3
  -- outputs at level 4: write the next round's banks, or (last round) accumulate
  let outV := vs[4]!
  let outM := pms[4]!
  let lastRound ← eqK rnd (rounds - 1)
  let writeEn ← and1 outV (← not1 lastRound)
  let w0 ← and1 writeEn (← not1 parity)   -- round r writes the banks of parity r
  let w1 ← and1 writeEn parity
  -- the last round's classes: sb = BCD of 2m for the pair entering level 3
  let v2 := vs[2]!
  let sbNext ← bcdInc (← bcdInc sb)
  let roundEnd0 ← and1 isDrain (← eqK drain 6)
  let sb' ← ite' roundEnd0 (← lit 12 0) (← ite' v2 sbNext sb)
  -- the address of s: s itself below 200, else f(s) (the BCD sum of its digits' squares)
  let small (x : Sig 12) : M ctx (Sig 1) := do ult x (← lit 12 0x200)
  let f (x : Sig 12) : M ctx (Sig 12) := do
    let p ← bcdAdd (← zx (← sq (← slice x 0 4)) 12) (← zx (← sq (← slice x 4 4)) 12)
    bcdAdd p (← zx (← sq (← slice x 8 4)) 12)
  let sOddB ← or sb (← lit 12 1)            -- 2m is even: its last digit + 1 needs no carry
  let ah' ← ite' (← small sOddB) sOddB (← f sOddB)
  let al' ← ite' (← small sb) sb (← f sb)
  let ch' ← readMem "classH" 1 ah
  let cl' ← readMem "classL" 1 al
  -- level 5: the pair's contribution (s = 0 is not a start)
  let lo0 ← eqK outM 0
  let hiPart ← ite' ch h4 zero
  let loPart ← ite' (← and1 cl (← not1 lo0)) l4 zero
  let ps' ← add hiPart loPart
  let pv' ← and1 outV lastRound
  let acc' ← ite' pv (← add acc ps) acc
  -- mode control
  let toDrain ← and1 streaming atEnd
  let drainEnd ← eqK drain 6
  let drain' ← ite' isDrain (← addK drain 1) (← lit 3 0)
  let nextRnd ← addK rnd 1
  let afterDrain ← ite' (← eqK nextRnd (rounds - 1)) (← lit 2 2) (← lit 2 0)
  let mode1 ← ite' toDrain (← lit 2 1) mode
  let mode2 ← ite' (← and1 isDrain drainEnd) afterDrain mode1
  let mode' ← ite' (← and1 isWait cdone) (← lit 2 0) mode2
  let roundEnd ← and1 isDrain drainEnd
  let rnd' ← ite' roundEnd nextRnd rnd
  let lim' ← ite' roundEnd (← addK lim 81) lim
  -- pairs up to ⌊(81·(rnd+1) + 3)/2⌋: the last ones flush the line with zeros
  let mendNext ← rom nextRnd AWB fun r => (81 * (r + 1) + 3) / 2
  let mend' ← ite' roundEnd mendNext mend
  let finished ← and1 (← eqK rnd rounds) (← and1 (← not1 pv) (← not1 done))
  let answer' ← ite' finished acc answer
  let done' ← or1 done finished
  let mkT (n1 n2 n3 : List (Sig W)) (n4 : Sig W) : Tree Sig :=
    { a0 := n1[0]!, a1 := n1[1]!, a2 := n1[2]!, a3 := n1[3]!, a4 := n1[4]!, b0 := n2[0]!, b1 := n2[1]!,
      b2 := n2[2]!, c0 := n3[0]!, c1 := n3[1]!, d := n4 }
  let vNext := [streaming, vs[0]!, vs[1]!, vs[2]!, vs[3]!]
  let pmNext := [m, pms[0]!, pms[1]!, pms[2]!, pms[3]!]
  let clsPort := port writeCls cs clsVal
  finish done answer
    ⟨{ rnd := rnd', m := m', mode := mode', drain := drain', mend := mend', lim := lim', sb := sb', ah := ah',
       al := al', ch := ch', cl := cl', ps := ps', pv := pv', acc := acc', done := done', answer := answer',
       cs := cs', part := part', cv := cv', sqh := sqh', phase := phase', cdone := cdone' },
     Lanes.ofFn fun k => ⟨vNext[k]!, pmNext[k]!⟩,
     Lanes.ofFn fun t => if t == 0 then mkT h1' h2' h3' h4' else mkT l1' l2' l3' l4',
     Lanes.ofFn fun k => ⟨line'[k]!⟩⟩
    (← writePorts [("be0", #[port w0 outM l4]), ("bo0", #[port w0 outM h4]), ("be1", #[port w1 outM l4]),
      ("bo1", #[port w1 outM h4]), ("classA", #[clsPort]), ("classH", #[clsPort]), ("classL", #[clsPort])])

def design : Except String Design := solverDesign ctx body

def problem : Problem :=
  { number := 92, title := "Square digit chains",
    idea := "Count 7-digit strings by digit-square sum with seven streamed convolution rounds, two sums per cycle (delay line, ten taps each, pipelined adder trees, ping-pong block RAMs by parity); classify the sums below 200 with a memoised BCD chain engine alongside, the others through their own digit-square sum.",
    answerWidth := W, design, reference, maxCycles := 10000 }

end HDLean.Euler.P092
