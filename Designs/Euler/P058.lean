import Designs.Euler.Kit

/-!
# Problem 58: spiral primes

The side length of the square spiral at which the share of primes along both
diagonals first falls below 10%.

The corners of the layer with odd side `s` are `s² − j(s − 1)`, `j = 1, 2, 3`
(the fourth, `s²`, is a square). The design walks the layers with additions only
(`s²` and `3(s + 1)` kept incrementally), and tests the corners for primality:

* **a filter**: `s mod p` for the 17 primes `p ≤ 61`, stepped by 2 per layer;
  a small table per prime says which corners `p` divides. About 70% of the
  corners stop here (from `s = 11` on, where no corner is one of these primes);
* **Miller–Rabin lanes** for the rest, with bases 2, 7 and 61 (deterministic
  below 4 759 123 141; the corners stay below `26241² < 2^30`). A lane works in
  Montgomery form with `R = 2^30`: `R mod n` by thirty modular doublings,
  squarings as fifteen radix-4 Montgomery steps on a carry-save pair
  (`(S, C) ← (S + C + d·x + q·n)/4`, two full-adder layers and no carry chain,
  `3x` and `3n` precomputed, `q` from the two low bits), the multiplications by
  the base as doublings and additions (`a` is a small constant) on one adder. The exponent's bits are
  read straight from `n` (`d = (n − 1)/2^r`);
* **a reorder buffer**: jobs go to any idle lane and finish out of order; their
  verdicts land in a 32-entry buffer, and a collector consumes them in order,
  layer by layer (a FIFO in block RAM holds each layer's job count), keeping
  `10·primes` and `2s − 1` to test the ratio.
-/
namespace HDLean.Euler.P058
open HDLean.Rtl HDLean.Rtl.Build

def isPrime (n : Nat) : Bool := Id.run do
  if n < 2 then return false
  let mut d := 2
  while d * d ≤ n do
    if n % d == 0 then return false
    d := d + 1
  return true

def reference (_ : Unit) : Nat := Id.run do
  let mut primes := 0
  let mut s := 1
  for _ in [:100000] do
    s := s + 2
    for j in [1:4] do
      if isPrime (s * s - j * (s - 1)) then primes := primes + 1
    if 10 * primes < 2 * s - 1 then return s
  return 0

def W : Nat := 16        -- the answer (a side length)
def NW : Nat := 30       -- corner values
def TW : Nat := 32       -- the lane's accumulator
def lanes : Nat := 5
def robBits : Nat := 5
def fifoBits : Nat := 6
def filterPrimes : List Nat := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61]
def bases : List Nat := [2, 7, 61]

/-! ## Registers -/

-- lane states (one-hot)
def sIdle := 0
def sScanR := 1
def sScanT := 2
def sN3 := 3       -- 3n, once per number
def sR1 := 4
def sBase := 5
def sDbl := 6
def sAdd := 7
def sAddFix := 8
def sExp := 9
def sX3 := 10      -- 3x, and a fresh carry-save accumulator
def sIter := 11    -- fifteen radix-4 Montgomery steps
def sRS := 12      -- absorb the pending carry
def sAD := 13      -- S + C
def sFin := 14     -- conditional subtraction
def sChk := 15
def sDec := 16
def sDone := 17
def nStates : Nat := 18
def SW : Nat := 35       -- carry-save words

hdl_record Lane where
  st : nStates := (1 <<< sIdle)
  n : NW
  r1 : NW
  x : NW
  x3 : TW
  n3 : TW
  t : TW
  S : SW
  C : SW
  ci : 1
  ib : 5
  tb : 5
  r : 5
  rr : 5
  mc : 5
  ab : 3
  bi : 2
  ph : 2
  tag : robBits
  lap : 1
  res : 1
  dq : 2
  eq1 : 1
  eqm : 1
  skip : 1

/-- The dispatcher: the corner walk, the layer's filter verdicts (registered, a
cycle into the layer), and a one-job slot between the corner walk and the lanes. -/
hdl_record Disp where
  s : W := 3
  sq : NW := 9
  f4 : 20 := 16
  t3 : 20 := 12
  sm1 : W := 2
  cn : NW := 7
  cj : 2 := 0
  lk : 2 := 0
  q : (robBits + 1) := 0
  wp : (fifoBits + 1) := 0
  wpd : (fifoBits + 1) := 0
  filt : 1 := 0
  hits : 3 := 0
  hv : 1 := 0
  pv : 1 := 0
  pn : NW
  ptag : robBits
  plap : 1

/-- A reorder buffer entry: verdict and lap (laps start at 1, so nothing is valid). -/
hdl_record RobEntry where
  rp : 1 := 0
  rl : 1 := 1

hdl_record Coll where
  h : (robBits + 1) := 0
  rptr : (fifoBits + 1) := 0
  sc : W := 3
  p10 : 20 := 0
  tt : 20 := 5
  krem : 2 := 0
  kv : 1 := 0
  done : 1 := 0
  answer : W := 0

/-- Lanes, dispatcher, the residues of the corner walk modulo the filter primes,
the reorder buffer and the collector. -/
abbrev State := Both (Lanes "l" lanes Lane) (Both Disp (Both (Lanes "res" filterPrimes.length (Word 7))
  (Both (Lanes "rob" (2 ^ robBits) RobEntry) Coll)))

def mems : Array MemSpec := #[ms "layers" fifoBits 2]

def ctx : Ctx := solverCtx "euler58" W State
  ⟨Lanes.replicate Lane.resets, Disp.resets, Lanes.ofFn fun i => ⟨.sync (3 % filterPrimes[i]!)⟩,
   Lanes.replicate RobEntry.resets, Coll.resets⟩ mems

/-- Bit `i` of `x`, for a 5-bit index. -/
def bitAt (x : Sig w) (i : Sig 5) : M ctx (Sig 1) := do
  pick i (← (List.range w).toArray.mapM fun k => bit x k)

/-- The bits of base `a` after its leading one, from the top: index `ab`. -/
def baseStart (a : Nat) : Nat := Nat.log2 a - 1

/-! ## A lane -/

structure LaneIO where
  idle : Sig 1
  doneReq : Sig 1
  tag : Sig robBits
  lap : Sig 1
  res : Sig 1
  deriving Inhabited

set_option maxRecDepth 20000 in
def lane (l : Nat) (rg : Lane Sig) (load : Sig 1) (nIn : Sig NW) (tagIn : Sig robBits) (lapIn : Sig 1)
    (granted : Sig 1) : M ctx (LaneIO × Lane Sig) := scope s!"lane {l}" do
  let st := rg.st
  let n := rg.n
  let r1 := rg.r1
  let x := rg.x
  let x3 := rg.x3
  let n3 := rg.n3
  let t := rg.t
  let sS := rg.S
  let sC := rg.C
  let ci := rg.ci
  let ib := rg.ib
  let tb := rg.tb
  let r := rg.r
  let rr := rg.rr
  let mc := rg.mc
  let ab := rg.ab
  let bi := rg.bi
  let ph := rg.ph
  let tag := rg.tag
  let lap := rg.lap
  let res := rg.res
  let dq := rg.dq
  let eq1 := rg.eq1
  let eqm := rg.eqm
  let skipR := rg.skip
  let is (k : Nat) : M ctx (Sig 1) := bit st k
  let isIdle ← is sIdle
  let isScanR ← is sScanR
  let isScanT ← is sScanT
  let isN3 ← is sN3
  let isR1 ← is sR1
  let isBase ← is sBase
  let isDbl ← is sDbl
  let isAdd ← is sAdd
  let isAddFix ← is sAddFix
  let isExp ← is sExp
  let isX3 ← is sX3
  let isIter ← is sIter
  let isRS ← is sRS
  let isAD ← is sAD
  let isFin ← is sFin
  let isChk ← is sChk
  let isDec ← is sDec
  let isDone ← is sDone
  let wide {k : Nat} (v : Sig k) : M ctx (Sig TW) := zx v TW
  let gate {k : Nat} (sel : Sig 1) (v : Sig k) : M ctx (Sig k) := do ite' sel v (← lit k 0)
  let nW ← wide n
  let xW ← wide x
  -- conditions
  let nBit ← bitAt n ib
  let mc29 ← eqK mc 29
  let mc14 ← eqK mc 14
  let aBits ← rom bi 8 fun i => bases.getD i 0
  let aStart ← rom bi 3 fun i => baseStart (bases.getD i 2)
  let aBit ← bitAt aBits (← zx ab 5)
  let abZero ← eqK ab 0
  -- n = a: this base says nothing (registered as the base is entered)
  let skip := skipR
  let lastBase ← eqK bi (bases.length - 1)
  let expEnd ← ult ib r
  let ph0 ← eqK ph 0
  let ph1 ← eqK ph 1
  let ph2 ← eqK ph 2
  let foundR ← and1 isScanR nBit
  let foundT ← and1 isScanT nBit
  let baseGo ← and1 isBase (← not1 skip)
  let baseSkip ← and1 isBase skip
  let r1Done ← and1 isR1 mc29
  let dblToAdd ← and1 isDbl aBit
  let dblNoAdd ← and1 isDbl (← not1 aBit)
  let dblDone ← and1 dblNoAdd abZero
  let dblStay ← and1 dblNoAdd (← not1 abZero)
  let addFixDone ← and1 isAddFix abZero
  let addFixMore ← and1 isAddFix (← not1 abZero)
  let mulaDone ← or1 dblDone addFixDone
  let finBit ← and1 isFin ph1
  let first := ph1
  let passD ← ite' first (← or1 eq1 eqm) eqm
  let lastTry ← ite' first (← eqK r 1) (← eqK rr 1)
  let failD ← and1 (← not1 passD) lastTry
  let contD ← and1 (← not1 passD) (← not1 lastTry)
  let nextBase ← or1 (← and1 isDec passD) baseSkip
  let prime ← and1 nextBase lastBase
  let composite ← and1 isDec failD
  let toDone ← or1 prime composite
  -- the adder, for everything but the Montgomery steps: A + B, gated sources
  let doubling ← or1 isR1 isDbl
  let reducing ← or1 doubling (← or1 isAddFix isFin)
  let fromX ← or1 isX3 isChk
  let fromT ← or1 isAdd (← or1 isAddFix isFin)
  let aOp ← or (← or (← gate doubling (← shlK t 1)) (← gate fromX xW))
    (← or (← gate fromT t) (← or (← gate isAD (← resize sS TW)) (← gate isN3 nW)))
  -- −n = ¬n | 1 for odd n; 1 for the load of t
  let negN ← or (← not nW) (← lit TW 1)
  let bOp ← or (← or (← gate isAdd xW) (← gate isX3 (← shlK xW 1)))
    (← or (← or (← gate isN3 (← shlK nW 1)) (← gate isAD (← resize sC TW)))
      (← or (← gate reducing negN) (← gate isChk (← wide r1))))
  let sum ← add aOp bOp
  let neg ← bit sum (TW - 1)
  let cs ← ite' (← and1 reducing neg) aOp sum   -- conditional subtraction of n
  let csN ← slice cs 0 NW
  -- a radix-4 Montgomery step on the carry-save pair (S, C) with pending carry ci:
  -- D = d·x, q chosen so that S + C + D + q·n + ci ≡ 0 mod 4, then shift by two
  let ext {k : Nat} (v : Sig k) : M ctx (Sig SW) := zx v SW
  let xS ← ext x
  let nS ← ext n
  let dX ← ite' (← bit dq 1) (← ite' (← bit dq 0) (← ext x3) (← shlK xS 1)) (← ite' (← bit dq 0) xS (← lit SW 0))
  let low ← add (← add (← slice sS 0 2) (← slice sC 0 2)) (← add (← slice dX 0 2) (← zx ci 2))
  let qv ← sub (← lit 2 0) (← mul low (← slice n 0 2))   -- n⁻¹ ≡ n (mod 4)
  let qN ← ite' (← bit qv 1) (← ite' (← bit qv 0) (← ext n3) (← shlK nS 1)) (← ite' (← bit qv 0) nS (← lit SW 0))
  -- in RS, D = Q = 0 and nothing is shifted: S + C + ci becomes exact
  let dIn ← gate isIter dX
  let qIn ← gate isIter qN
  let s1 ← xor (← xor sS sC) dIn
  let c1 ← or (← shlK (← or (← and sS sC) (← and (← or sS sC) dIn)) 1) (← zx ci SW)
  let s2 ← xor (← xor s1 qIn) c1
  let c2 ← shlK (← or (← and s1 qIn) (← and (← or s1 qIn) c1)) 1
  let cout ← bit c2 1
  let sNext ← ite' isIter (← shrK s2 2) s2
  let cNext ← ite' isIter (← shrK c2 2) c2
  -- next state (one-hot)
  let mut nxt : Array (Sig 1) := Array.replicate nStates ⟨0⟩
  let set (k : Nat) (v : Sig 1) (a : Array (Sig 1)) : Array (Sig 1) := a.set! k v
  nxt := set sIdle (← or1 (← and1 isIdle (← not1 load)) (← and1 isDone granted)) nxt
  nxt := set sScanR (← or1 (← and1 isIdle load) (← and1 isScanR (← not1 nBit))) nxt
  nxt := set sScanT (← or1 foundR (← and1 isScanT (← not1 nBit))) nxt
  nxt := set sN3 foundT nxt
  nxt := set sR1 (← or1 isN3 (← and1 isR1 (← not1 mc29))) nxt
  nxt := set sBase (← or1 r1Done (← and1 nextBase (← not1 lastBase))) nxt
  nxt := set sDbl (← or1 (← or1 baseGo dblStay) (← or1 addFixMore (← and1 finBit nBit))) nxt
  nxt := set sAdd dblToAdd nxt
  nxt := set sAddFix isAdd nxt
  nxt := set sExp (← or1 mulaDone (← and1 finBit (← not1 nBit))) nxt
  nxt := set sX3 (← or1 (← and1 isExp (← not1 expEnd)) (← and1 isDec contD)) nxt
  nxt := set sIter (← or1 isX3 (← and1 isIter (← not1 mc14))) nxt
  nxt := set sRS (← and1 isIter mc14) nxt
  nxt := set sAD isRS nxt
  nxt := set sFin isAD nxt
  nxt := set sChk (← or1 (← and1 isExp expEnd) (← and1 isFin ph2)) nxt
  nxt := set sDec isChk nxt
  nxt := set sDone (← or1 toDone (← and1 isDone (← not1 granted))) nxt
  let mut st' ← lit nStates 0
  for k in [0:nStates] do
    st' ← or st' (← shlK (← zx nxt[k]! nStates) k)
  -- registers
  let loading ← and1 isIdle load
  let n' ← ite' loading nIn n
  let tag' ← ite' loading tagIn tag
  let lap' ← ite' loading lapIn lap
  let r1' ← ite' r1Done csN r1
  let x' ← ite' baseGo r1 (← ite' (← or1 mulaDone isFin) csN x)
  let x3' ← ite' isX3 sum x3
  let n3' ← ite' isN3 sum n3
  -- t: 1 when the top bit is found (then 30 doublings give R mod n), R mod n for a
  -- new base, the doublings and additions, S + C, the final subtraction
  -- (the loads of 1 and of R mod n bypass the adder)
  let tEn ← or1 isR1 (← or1 (← or1 isDbl isAdd) (← or1 isAddFix (← or1 isAD isFin)))
  let t' ← ite' foundT (← lit TW 1) (← ite' baseGo (← wide r1) (← ite' tEn cs t))
  let csaEn ← or1 isIter isRS
  let zeroS ← lit SW 0
  let sS' ← ite' isX3 zeroS (← ite' csaEn sNext sS)
  let sC' ← ite' isX3 zeroS (← ite' csaEn cNext sC)
  let ci' ← ite' isX3 (← lit 1 0) (← ite' isIter cout (← ite' isRS (← lit 1 0) ci))
  let five (v : Nat) : M ctx (Sig 5) := lit 5 v
  let ib' ← ite' loading (← five 1) (← ite' (← and1 isScanR (← not1 nBit)) (← addK ib 1)
    (← ite' foundR (← five 29) (← ite' (← and1 isScanT (← not1 nBit)) (← subK ib 1)
    (← ite' (← and1 mulaDone ph0) (← subK tb 1)
    (← ite' (← or1 (← and1 mulaDone ph1) (← and1 finBit (← not1 nBit))) (← subK ib 1) ib)))))
  let tb' ← ite' foundT ib tb
  let r' ← ite' foundR ib r
  let startSquares ← and1 isDec (← and1 first contD)
  let rr' ← ite' startSquares (← subK r 1) (← ite' (← and1 isDec (← and1 ph2 contD)) (← subK rr 1) rr)
  let mc' ← ite' (← or1 isN3 isX3) (← five 0) (← ite' (← or1 isR1 isIter) (← addK mc 1) mc)
  let ab' ← ite' (← or1 baseGo (← and1 finBit nBit)) aStart
    (← ite' (← or1 dblStay addFixMore) (← subK ab 1) ab)
  let bi' ← ite' r1Done (← lit 2 0) (← ite' nextBase (← addK bi 1) bi)
  let ph' ← ite' baseGo (← lit 2 0) (← ite' (← and1 mulaDone ph0) (← lit 2 1) (← ite' startSquares (← lit 2 2) ph))
  let res' ← ite' toDone prime res
  -- the next Montgomery digit of x, a cycle ahead: x[2i+1 : 2i]
  let digits ← (List.range 16).toArray.mapM fun i => if 2 * i + 1 < NW then slice x (2 * i) 2 else lit 2 0
  let dq' ← ite' isX3 (← slice x 0 2) (← ite' isIter (← pick (← addK mc 1) digits) dq)
  -- the checks' comparisons (x is stable): x = R mod n; x + R mod n = n
  let skipNext ← ite' r1Done (← eq nW (← lit TW (bases.getD 0 0)))
    (← ite' nextBase (← eq nW (← zx (← rom (← addK bi 1) 8 fun i => bases.getD i 0) TW)) skipR)
  let eq1' ← eq x r1
  let eqm' ← and1 (← eq (← slice sum 0 NW) n) (← eqK (← slice sum NW (TW - NW)) 0)
  pure (⟨isIdle, isDone, tag, lap, res⟩,
    { st := st', n := n', r1 := r1', x := x', x3 := x3', n3 := n3', t := t', S := sS', C := sC', ci := ci',
      ib := ib', tb := tb', r := r', rr := rr', mc := mc', ab := ab', bi := bi', ph := ph', tag := tag',
      lap := lap', res := res', dq := dq', eq1 := eq1', eqm := eqm', skip := skipNext })

/-! ## Dispatcher, reorder buffer, collector -/

/-- Which corners `s² − j(s − 1)` (bit `j − 1`) a prime divides, by `s mod p`. -/
def divides (p : Nat) (rsd : Nat) : Nat :=
  (List.range 3).foldl (fun acc j =>
    let v := (rsd * rsd + (j + 1) * (p - (rsd + p - 1) % p)) % p
    if v == 0 then acc ||| (1 <<< j) else acc) 0

set_option maxRecDepth 20000 in
def body : M ctx Wiring := solver "P058" State fun ⟨laneRs, d, residR, rob, co⟩ => do
  let lrs := laneRs.lanes.toArray
  -- dispatcher state
  let s := d.s
  let sq := d.sq
  let f4 := d.f4
  let t3 := d.t3
  let sm1 := d.sm1
  let cn := d.cn
  let cj := d.cj
  let lk := d.lk
  let q := d.q
  let wp := d.wp
  let wpd := d.wpd
  let filt := d.filt
  let resids := (residR.lanes.map (·.v)).toArray
  let hitsR := d.hits
  let hv := d.hv
  let pv := d.pv
  let pn := d.pn
  let ptag := d.ptag
  let plap := d.plap
  -- collector state
  let h := co.h
  let rptr := co.rptr
  let sc := co.sc
  let p10 := co.p10
  let tt := co.tt
  let krem := co.krem
  let kv := co.kv
  let done := co.done
  let answer := co.answer
  -- the filter: corners divisible by a small prime (from s = 11 on)
  let mut mask ← lit 3 0
  for (p, i) in filterPrimes.zipIdx do
    mask ← or mask (← rom resids[i]! 3 (divides p))
  let hits ← ite' filt mask (← lit 3 0)
  let survives ← not1 (← bit (← lshr hitsR (← zx cj 3)) 0)
  -- window and FIFO room
  let inFlight ← sub q h
  let windowOk ← ltK inFlight (2 ^ robBits)
  let lastCorner ← eqK cj 2
  let fifoUsed ← sub wp rptr
  let fifoOk ← ltK fifoUsed (2 ^ fifoBits)
  -- lanes: the lowest idle lane takes the job
  let robTag ← slice q 0 robBits
  let robLap ← bit q robBits
  let mut taken ← lit 1 0
  let mut loads : Array (Sig 1) := #[]
  let mut idleAny ← lit 1 0
  -- lanes' idle flags first (from their state registers)
  let idles ← lrs.toList.mapM fun rg => bit rg.st sIdle
  for l in [0:lanes] do
    idleAny ← or1 idleAny idles[l]!
  -- the slot's job goes to the lowest idle lane
  let consumed ← and1 pv idleAny
  for l in [0:lanes] do
    let g ← and1 idles[l]! (← not1 taken)
    loads := loads.push (← and1 pv g)
    taken ← or1 taken idles[l]!
  -- a surviving corner enters the slot when it is free (or being emptied)
  let slotFree ← or1 (← not1 pv) consumed
  let roomOk ← or1 (← not1 lastCorner) fifoOk
  let walking ← and1 hv (← not1 done)
  let dispatch ← and1 walking (← and1 survives (← and1 slotFree (← and1 windowOk roomOk)))
  -- ROB write arbitration: the lowest finished lane
  let dones ← lrs.toList.mapM fun rg => bit rg.st sDone
  let mut wtaken ← lit 1 0
  let mut grants : Array (Sig 1) := #[]
  for l in [0:lanes] do
    grants := grants.push (← and1 dones[l]! (← not1 wtaken))
    wtaken ← or1 wtaken dones[l]!
  let mut laneNext : Array (Lane Sig) := #[]
  let mut ios : Array LaneIO := #[]
  for l in [0:lanes] do
    let (io, rg') ← lane l lrs[l]! loads[l]! pn ptag plap grants[l]!
    laneNext := laneNext.push rg'
    ios := ios.push io
  -- the granted lane's verdict
  let mut wTag ← lit robBits 0
  let mut wLap ← lit 1 0
  let mut wRes ← lit 1 0
  for l in [0:lanes] do
    wTag ← ite' grants[l]! ios[l]!.tag wTag
    wLap ← ite' grants[l]! ios[l]!.lap wLap
    wRes ← ite' grants[l]! ios[l]!.res wRes
  -- dispatcher: advance a corner when it is filtered out or dispatched
  let advance ← and1 walking (← and1 (← or1 (← not1 survives) dispatch) roomOk)
  let layerEnd ← and1 advance lastCorner
  let lk1 ← ite' dispatch (← addK lk 1) lk
  let q' ← ite' dispatch (← addK q 1) q
  let cn' ← ite' layerEnd (← resize (← add (← zx sq NW) (← zx t3 NW)) NW)
    (← ite' advance (← sub cn (← zx sm1 NW)) cn)
  let cj' ← ite' layerEnd (← lit 2 0) (← ite' advance (← addK cj 1) cj)
  let lk' ← ite' layerEnd (← lit 2 0) lk1
  let s' ← ite' layerEnd (← addK s 2) s
  let sq' ← ite' layerEnd (← add sq (← zx f4 NW)) sq
  let f4' ← ite' layerEnd (← addK f4 8) f4
  let t3' ← ite' layerEnd (← addK t3 6) t3
  let sm1' ← ite' layerEnd (← addK sm1 2) sm1
  let wp' ← ite' layerEnd (← addK wp 1) wp
  let filt' ← or1 filt (← and1 layerEnd (← eqK s 9))
  let mut residNext : Array (Sig 7) := #[]
  for (p, i) in filterPrimes.zipIdx do
    let v ← addK resids[i]! 2
    let wrapped ← ite' (← geK v p) (← subK v p) v
    residNext := residNext.push (← ite' layerEnd wrapped resids[i]!)
  let hitsR' ← ite' hv hitsR hits
  let hv' ← and1 (← or1 hv (← lit 1 1)) (← not1 layerEnd)
  let pv' ← or1 dispatch (← and1 pv (← not1 consumed))
  let pn' ← ite' dispatch cn pn
  let ptag' ← ite' dispatch robTag ptag
  let plap' ← ite' dispatch robLap plap
  let fifoAddr ← slice wp 0 fifoBits
  let fifoWrite := port layerEnd fifoAddr lk1
  -- the reorder buffer
  let mut robNext : Array (RobEntry Sig) := #[]
  let mut robP : Array (Sig 1) := #[]
  let mut robL : Array (Sig 1) := #[]
  for (en, e) in rob.lanes.zipIdx do
    let rpE := en.rp
    let rlE := en.rl
    let hit ← and1 wtaken (← eqK wTag e)
    robNext := robNext.push ⟨← ite' hit wRes rpE, ← ite' hit wLap rlE⟩
    robP := robP.push rpE
    robL := robL.push rlE
  -- the collector
  let hIdx ← slice h 0 robBits
  let hLap ← bit h robBits
  let entryP ← pick hIdx robP
  let entryL ← pick hIdx robL
  let ready ← eq entryL hLap
  let fifoHas ← ne rptr wpd
  let layerCount ← readMem "layers" 2 (← slice rptr 0 fifoBits)
  let running ← not1 done
  let loadK ← and1 running (← and1 (← not1 kv) fifoHas)
  let kZero ← eqK krem 0
  let consume ← and1 running (← and1 kv (← and1 (← not1 kZero) ready))
  let layerDone ← and1 running (← and1 kv kZero)
  let below ← ult p10 tt
  let found ← and1 layerDone below
  let nextLayer ← and1 layerDone (← not1 below)
  let h' ← ite' consume (← addK h 1) h
  let rptr' ← ite' loadK (← addK rptr 1) rptr
  let krem' ← ite' loadK layerCount (← ite' consume (← subK krem 1) krem)
  let kv' ← ite' loadK (← lit 1 1) (← ite' nextLayer (← lit 1 0) kv)
  let p10' ← ite' (← and1 consume entryP) (← addK p10 10) p10
  let sc' ← ite' nextLayer (← addK sc 2) sc
  let tt' ← ite' nextLayer (← addK tt 4) tt
  let answer' ← ite' found sc answer
  let done' ← or1 done found
  finish done answer
    ⟨Lanes.ofFn fun l => laneNext.getD l default,
     { s := s', sq := sq', f4 := f4', t3 := t3', sm1 := sm1', cn := cn', cj := cj', lk := lk', q := q', wp := wp',
       wpd := wp, filt := filt', hits := hitsR', hv := hv', pv := pv', pn := pn', ptag := ptag', plap := plap' },
     Lanes.ofFn fun i => ⟨residNext.getD i default⟩,
     Lanes.ofFn fun e => robNext.getD e default,
     { h := h', rptr := rptr', sc := sc', p10 := p10', tt := tt', krem := krem', kv := kv', done := done',
       answer := answer' }⟩
    (← writePorts [("layers", #[fifoWrite])])

def design : Except String Design := solverDesign ctx body

def problem : Problem :=
  { number := 58, title := "Spiral primes",
    idea := "Layer corners by additions only; a filter of residues modulo the primes up to 61; five Miller–Rabin lanes (bases 2, 7, 61) in Montgomery form, one adder each; a reorder buffer and an in-order collector testing the ratio layer by layer.",
    answerWidth := W, design, reference, maxCycles := 10000000 }

end HDLean.Euler.P058
