import Designs.Euler.Kit

/-!
# Problem 48: self powers

The last ten digits of `1^1 + 2^2 + … + 1000^1000`.

Modulo `10^10 = 2^10 · 5^10`, by the Chinese remainder theorem: every term is
computed modulo `5^10` (24-bit residues) and modulo `2^10`, the two sums are
combined once at the end. Terms `n^n` with `10 | n` vanish (`10^n` divides them)
and are skipped.

Six lanes take the exponents from a shared counter. A lane runs left-to-right
square-and-multiply: squarings modulo `5^10` on a radix-4 interleaved multiplier
(`acc ← 4·acc + d·B mod M`, twelve digits, the seven candidate reductions
`4·acc + d·B − k·M` side by side, the next digit's `d·B − k·M` precomputed), the
multiplications by `n` on the same multiplier with only the five digits of `n`;
alongside, the residue modulo `2^10` is squared and multiplied by a ten-bit
multiplier. Each lane keeps its own two sums; at the end they are added and the
two residues combined: `X = s5 + 5^10 · ((s2 − s5) · 5^-10 mod 2^10)`.
-/
namespace HDLean.Euler.P048
open HDLean.Rtl HDLean.Rtl.Build

def MOD5 : Nat := 5 ^ 10
def MOD : Nat := 10 ^ 10
def limit : Nat := 1000

def reference (_ : Unit) : Nat :=
  (List.range limit).foldl (fun acc i => (acc + Nat.pow (i + 1) (i + 1)) % MOD) 0

/-- `5^-10 mod 2^10`. -/
def inv5 : Nat := ((List.range 1024).find? fun t => (t * MOD5) % 1024 == 1).getD 0

def MW : Nat := 24       -- residues modulo 5^10
def YW : Nat := 28       -- candidate reductions, two's complement
def W : Nat := 34
def lanes : Nat := 6

def ks : List Nat := List.range 7

-- lane states
def sIdle := 0
def sNext := 1     -- next exponent bit: square, or finish
def sPrep := 2     -- reductions for the first digit
def sMul := 3
def sAfter := 4    -- multiplication finished
def sAdd := 5      -- add the term to the lane's sums

hdl_record Lane where
  st : 3 := sIdle
  n : 10
  x : MW
  x2 : 10
  bi : 4
  isn : 1
  a : MW
  b : (MW + 1)
  b3 : (MW + 2)
  acc : MW
  cnt : 4
  s5 : MW := 0
  s2 : 10 := 0
  y0 : YW
  y1 : YW
  y2 : YW
  y3 : YW
  y4 : YW
  y5 : YW
  y6 : YW

hdl_record Glob where
  nn : 10 := 1
  u10 : 4 := 1      -- nn mod 10
  left : 1 := 1
  scan : 4 := 0
  t5 : MW := 0
  t2 : 10 := 0
  fin : 3 := 0
  tt : 10 := 0
  acc : W := 0
  mb : W := 0
  done : 1 := 0
  answer : W := 0

abbrev State := Both (Lanes "l" lanes Lane) Glob

def ctx : Ctx := solverCtx "euler48" W State ⟨Lanes.replicate Lane.resets, Glob.resets⟩

/-- `d·B − k·M` for each `k`, as two's complement, for the digit `d`. -/
def reductions (d : Sig 2) (b : Sig (MW + 1)) (b3 : Sig (MW + 2)) : M ctx (List (Sig YW)) := do
  let d1 ← bit d 0
  let d2 ← bit d 1
  let bY ← zx b YW
  let b2 ← shlK bY 1
  let b3Y ← zx b3 YW
  let zero ← lit YW 0
  let lo ← ite' d1 bY zero
  let hi ← ite' d1 b3Y b2
  let dB ← ite' d2 hi lo
  ks.mapM fun k => subK dB (k * MOD5)

/-- `x + y mod 5^10`, for `x, y < 5^10`. -/
def addMod (x y : Sig MW) : M ctx (Sig MW) := do
  let s ← add (← zx x (MW + 1)) (← zx y (MW + 1))
  let t ← subK s MOD5
  slice (← ite' (← bit t MW) s t) 0 MW

structure LaneIO where
  idle : Sig 1
  s5 : Sig MW
  s2 : Sig 10
  deriving Inhabited

set_option maxRecDepth 20000 in
def lane (l : Nat) (r : Lane Sig) (load : Sig 1) (nIn : Sig 10) : M ctx (LaneIO × Lane Sig) := scope s!"lane {l}" do
  let st := r.st
  let n := r.n
  let x := r.x
  let x2 := r.x2
  let bi := r.bi
  let isn := r.isn
  let a := r.a
  let b := r.b
  let b3 := r.b3
  let acc := r.acc
  let cnt := r.cnt
  let s5 := r.s5
  let s2 := r.s2
  let ys := [r.y0, r.y1, r.y2, r.y3, r.y4, r.y5, r.y6]
  let isIdle ← eqK st sIdle
  let isNext ← eqK st sNext
  let isPrep ← eqK st sPrep
  let isMul ← eqK st sMul
  let isAfter ← eqK st sAfter
  let isAdd ← eqK st sAdd
  -- one radix-4 step: 4·acc + d·B − k·M, keep the last non-negative one
  let acc4 ← shlK (← zx acc YW) 2
  let ts ← ys.mapM fun y => add acc4 y
  let mut red ← slice ts[0]! 0 MW
  for k in [1:7] do
    red ← ite' (← bit ts[k]! (YW - 1)) red (← slice ts[k]! 0 MW)
  let dNext ← ite' isPrep (← slice a (MW - 2) 2) (← slice a (MW - 4) 2)
  let ys' ← reductions dNext b b3
  let cnt0 ← eqK cnt 0
  -- the exponent: bits of n below the top one, from bi down; bi = 15 when finished
  let nBit ← bit (← lshr n (← zx bi 10)) 0
  let finished ← eqK bi 15
  let topIdx ← bitLen n 4      -- the top bit's index + 1
  -- starting a multiplication: a squaring (A = x, 12 digits) or by n (A = n at the top, 5 digits)
  let startSq ← and1 isNext (← not1 finished)
  let startN ← and1 isAfter (← and1 (← not1 isn) nBit)
  let start ← or1 startSq startN
  let aSq := x
  let aN ← shlK (← zx n MW) (MW - 10)
  -- B: x, or (multiplying by n right after a squaring) the square just computed
  let bSrc ← ite' isAfter acc x
  let xB ← zx bSrc (MW + 1)
  let x3 ← add (← zx bSrc (MW + 2)) (← shlK (← zx bSrc (MW + 2)) 1)
  -- after a multiplication: next bit (after the squaring, multiply by n if the bit is set)
  let afterSq ← and1 isAfter (← not1 isn)
  let leaveBit ← or1 (← and1 afterSq (← not1 nBit)) (← and1 isAfter isn)
  -- residues modulo 2^10
  let x2sq ← mul x2 x2
  let x2n ← mul x2 n
  -- states
  let k3 (v : Nat) : M ctx (Sig 3) := lit 3 v
  let mut st' := st
  st' ← ite' (← and1 isIdle load) (← k3 sNext) st'
  st' ← ite' startSq (← k3 sPrep) st'
  st' ← ite' (← and1 isNext finished) (← k3 sAdd) st'
  st' ← ite' isPrep (← k3 sMul) st'
  st' ← ite' (← and1 isMul cnt0) (← k3 sAfter) st'
  st' ← ite' isAfter (← ite' startN (← k3 sPrep) (← k3 sNext)) st'
  st' ← ite' isAdd (← k3 sIdle) st'
  let loading ← and1 isIdle load
  let n' ← ite' loading nIn n
  let x' ← ite' loading (← zx nIn MW) (← ite' isAfter acc x)
  let x2' ← ite' loading nIn (← ite' afterSq x2sq (← ite' (← and1 isAfter isn) x2n x2))
  let topLoad ← bitLen nIn 4
  let bi' ← ite' loading (← subK topLoad 2) (← ite' leaveBit (← subK bi 1) bi)
  let isn' ← ite' startN (← lit 1 1) (← ite' startSq (← lit 1 0) isn)
  let a' ← ite' start (← ite' startN aN aSq) (← ite' isMul (← shlK a 2) a)
  let b' ← ite' start xB b
  let b3' ← ite' start x3 b3
  let acc' ← ite' start (← lit MW 0) (← ite' isMul red acc)
  let cnt' ← ite' start (← ite' startN (← lit 4 4) (← lit 4 11)) (← ite' isMul (← subK cnt 1) cnt)
  let s5' ← ite' isAdd (← addMod s5 x) s5
  let s2' ← ite' isAdd (← add s2 x2) s2
  let _ := topIdx
  let y := ys'.toArray
  pure (⟨isIdle, s5, s2⟩,
    { st := st', n := n', x := x', x2 := x2', bi := bi', isn := isn', a := a', b := b', b3 := b3', acc := acc',
      cnt := cnt', s5 := s5', s2 := s2', y0 := y[0]!, y1 := y[1]!, y2 := y[2]!, y3 := y[3]!, y4 := y[4]!,
      y5 := y[5]!, y6 := y[6]! })

set_option maxRecDepth 20000 in
def body : M ctx Wiring := solver "P048" State fun ⟨ls, g⟩ => do
  let nn := g.nn
  let u10 := g.u10
  let left := g.left
  let scan := g.scan
  let t5 := g.t5
  let t2 := g.t2
  let fin := g.fin
  let tt := g.tt
  let acc := g.acc
  let mb := g.mb
  let done := g.done
  let answer := g.answer
  let lrs := ls.lanes.toArray
  -- exponents 1 … 1000, skipping multiples of 10, to the lowest idle lane
  let idles ← lrs.toList.mapM fun r => eqK r.st sIdle
  let mut taken ← lit 1 0
  let mut next : Array (Lane Sig) := #[]
  let mut ios : Array LaneIO := #[]
  let mut idleAny ← lit 1 0
  for l in [0:lanes] do
    idleAny ← or1 idleAny idles[l]!
  let skip ← eqK u10 0
  let give ← and1 left (← and1 (← not1 skip) idleAny)
  for l in [0:lanes] do
    let load ← and1 give (← and1 idles[l]! (← not1 taken))
    taken ← or1 taken idles[l]!
    let (io, r') ← lane l lrs[l]! load nn
    next := next.push r'
    ios := ios.push io
  let advance ← and1 left (← or1 skip give)
  let lastN ← eqK nn limit
  let nn' ← ite' advance (← addK nn 1) nn
  let u10' ← ite' advance (← ite' (← eqK u10 9) (← lit 4 0) (← addK u10 1)) u10
  let left' ← and1 left (← not1 (← and1 advance lastN))
  -- the end: add the lanes' sums, then combine the residues
  let allIdle ← allTree (ios.toList.map (·.idle))
  let quiet ← and1 (← not1 left) allIdle
  let scanning ← and1 quiet (← ltK scan lanes)
  let t5' ← ite' scanning (← addMod t5 (← pick scan (ios.map (·.s5)))) t5
  let t2' ← ite' scanning (← add t2 (← pick scan (ios.map (·.s2)))) t2
  let scan' ← ite' scanning (← addK scan 1) scan
  -- fin: 0 summing, 1 t = (t2 − t5)·5^-10 mod 2^10, 2 … : X = t5 + 5^10·t, serially over t's bits
  let summed ← and1 quiet (← eqK scan lanes)
  let f0 ← and1 summed (← eqK fin 0)
  let f1 ← eqK fin 1
  let f2 ← eqK fin 2
  let diff ← sub t2 (← resize t5 10)
  let tt' ← ite' f0 (← mulK diff inv5) (← ite' f2 (← shrK tt 1) tt)
  let acc' ← ite' f0 (← zx t5 W) (← ite' (← and1 f2 (← bit tt 0)) (← add acc mb) acc)
  let mb' ← ite' f0 (← lit W MOD5) (← ite' f2 (← shlK mb 1) mb)
  let ttZero ← eqK tt 0
  let fin' ← ite' f0 (← lit 3 1) (← ite' f1 (← lit 3 2) (← ite' (← and1 f2 ttZero) (← lit 3 3) fin))
  let finished ← and1 (← eqK fin 3) (← not1 done)
  let answer' ← ite' finished acc answer
  let done' ← or1 done finished
  finish done answer ⟨Lanes.ofFn fun l => next.getD l default,
    { nn := nn', u10 := u10', left := left', scan := scan', t5 := t5', t2 := t2', fin := fin', tt := tt',
      acc := acc', mb := mb', done := done', answer := answer' }⟩

def design : Except String Design := solverDesign ctx body

def problem : Problem :=
  { number := 48, title := "Self powers",
    idea := "By the Chinese remainder theorem, modulo 5^10 and 2^10: six lanes of square-and-multiply on radix-4 interleaved modular multipliers (multiplications by n use only its five digits), terms with 10 | n skipped, the residues combined once at the end.",
    answerWidth := W, design, reference, maxCycles := 1000000 }

end HDLean.Euler.P048
