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

-- DP control: round, input pair, mode (0 stream, 1 drain, 2 wait), drain counter,
-- the round's last pair and the input limit 81·rnd
def dpRegs : List RegSpec :=
  [rs "rnd" 3 (.sync 0), rs "m" AWB (.sync 0), rs "mode" 2 (.sync 0), rs "drain" 3 (.sync 0),
   rs "mend" AWB (.sync ((81 + 3) / 2)), rs "lim" 10 (.sync 0)]
-- pipeline levels 0 … 4 (taps, l1, l2, l3, l4): valid and pair index
def pipeRegs : List RegSpec :=
  (List.range 5).map (fun k => rs s!"v{k}" 1 (.sync 0)) ++ (List.range 5).map (fun k => rs s!"pm{k}" AWB)
-- two adder trees (hi: s = 2m+1, lo: s = 2m)
def treeRegs : List RegSpec :=
  ["h", "l"].flatMap fun t =>
    (List.range 5).map (fun k => rs s!"{t}1_{k}" W) ++ (List.range 3).map (fun k => rs s!"{t}2_{k}" W) ++
    (List.range 2).map (fun k => rs s!"{t}3_{k}" W) ++ [rs s!"{t}4" W]
-- last round: BCD of 2m at level 2, the class table addresses (level 3), classes
-- (level 4), the masked pair sum (level 5)
def lastRegs : List RegSpec :=
  [rs "sb" 12 (.sync 0), rs "ah" 12, rs "al" 12, rs "ch" 1, rs "cl" 1, rs "ps" W, rs "pv" 1 (.sync 0),
   rs "acc" W (.sync 0), rs "done" 1 (.sync 0), rs "answer" W (.sync 0)]
-- classifier (values in BCD)
def classRegs : List RegSpec :=
  [rs "cs" 12 (.sync 1), rs "part" 12, rs "cv" 12 (.sync 1), rs "sqh" 8, rs "phase" 1 (.sync 0),
   rs "cdone" 1 (.sync 0)]
def lineRegs : List RegSpec := (List.range LINE).map fun k => rs s!"d{k}" W (.sync 0)

def regs : Array RegSpec := (dpRegs ++ pipeRegs ++ treeRegs ++ lastRegs ++ classRegs ++ lineRegs).toArray
def iPipe := dpRegs.length
def iTree := iPipe + pipeRegs.length
def iLast := iTree + treeRegs.length
def iClass := iLast + lastRegs.length
def iLine := iClass + classRegs.length

/-- Banks: even and odd `s`, for rounds of each parity; three copies of the class
table (classifier, hi lookup, lo lookup), indexed by BCD. -/
def mems : Array MemSpec := #[ms "be0" AWB W, ms "bo0" AWB W, ms "be1" AWB W, ms "bo1" AWB W,
  ms "classA" 12 1, ms "classH" 12 1, ms "classL" 12 1]

def ctx : Ctx := solverCtx "euler92" W regs mems

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
def body : M ctx Wiring := do
  let rnd ← rd 0 3
  let m ← rd 1 AWB
  let mode ← rd 2 2
  let drain ← rd 3 3
  let mend ← rd 4 AWB
  let lim ← rd 5 10
  let vs ← (List.range 5).mapM fun k => rd (iPipe + k) 1
  let pms ← (List.range 5).mapM fun k => rd (iPipe + 5 + k) AWB
  let tree (t : Nat) : M ctx (List (Sig W) × List (Sig W) × List (Sig W) × Sig W) := do
    let base := iTree + 11 * t
    pure (← (List.range 5).mapM fun k => rd (base + k) W, ← (List.range 3).mapM fun k => rd (base + 5 + k) W,
      ← (List.range 2).mapM fun k => rd (base + 8 + k) W, ← rd (base + 10) W)
  let (h1, h2, h3, h4) ← tree 0
  let (l1, l2, l3, l4) ← tree 1
  let sb ← rd iLast 12
  let ah ← rd (iLast + 1) 12
  let al ← rd (iLast + 2) 12
  let ch ← rd (iLast + 3) 1
  let cl ← rd (iLast + 4) 1
  let ps ← rd (iLast + 5) W
  let pv ← rd (iLast + 6) 1
  let acc ← rd (iLast + 7) W
  let done ← rd (iLast + 8) 1
  let answer ← rd (iLast + 9) W
  let cs ← rd iClass 12
  let part ← rd (iClass + 1) 12
  let cv ← rd (iClass + 2) 12
  let sqh ← rd (iClass + 3) 8
  let phase ← rd (iClass + 4) 1
  let cdone ← rd (iClass + 5) 1
  let line ← (List.range LINE).mapM fun k => rd (iLine + k) W
  -- the classifier: one chain step per two cycles (test and two squares, then
  -- the third square), in BCD; the class table is memoised
  let cv1 ← eqK cv 1
  let cv89 ← eqK cv 0x89
  let below ← ult cv cs
  let known ← memRead 4 1 cv
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
  let e0 ← memRead 0 W m
  let o0 ← memRead 1 W m
  let e1 ← memRead 2 W m
  let o1 ← memRead 3 W m
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
  let ch' ← memRead 5 1 ah
  let cl' ← memRead 6 1 al
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
  let treeRefs (n1 n2 n3 : List (Sig W)) (n4 : Sig W) : Array Nat :=
    (n1.map (·.ref)).toArray ++ (n2.map (·.ref)).toArray ++ (n3.map (·.ref)).toArray ++ #[n4.ref]
  let nexts := #[rnd'.ref, m'.ref, mode'.ref, drain'.ref, mend'.ref, lim'.ref,
      streaming.ref, vs[0]!.ref, vs[1]!.ref, vs[2]!.ref, vs[3]!.ref,
      m.ref, pms[0]!.ref, pms[1]!.ref, pms[2]!.ref, pms[3]!.ref] ++
    treeRefs h1' h2' h3' h4' ++ treeRefs l1' l2' l3' l4' ++
    #[sb'.ref, ah'.ref, al'.ref, ch'.ref, cl'.ref, ps'.ref, pv'.ref, acc'.ref, done'.ref, answer'.ref,
      cs'.ref, part'.ref, cv'.ref, sqh'.ref, phase'.ref, cdone'.ref] ++
    (line'.map (·.ref)).toArray
  let clsPort := port writeCls cs clsVal
  let writes := #[#[port w0 outM l4], #[port w0 outM h4], #[port w1 outM l4], #[port w1 outM h4],
    #[clsPort], #[clsPort], #[clsPort]]
  pure (solverWiring ⟨done, answer.ref, nexts, writes⟩)

def design : Design := single ctx body

def problem : Problem :=
  { number := 92, title := "Square digit chains",
    idea := "Count 7-digit strings by digit-square sum with seven streamed convolution rounds, two sums per cycle (delay line, ten taps each, pipelined adder trees, ping-pong block RAMs by parity); classify the sums below 200 with a memoised BCD chain engine alongside, the others through their own digit-square sum.",
    answerWidth := W, design, reference, maxCycles := 10000 }

end HDLean.Euler.P092
