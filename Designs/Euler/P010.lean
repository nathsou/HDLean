import Designs.Euler.Kit

/-!
# Problem 10: summation of primes

The sum of the primes below two million.

A segmented sieve of Eratosthenes over the odd numbers, in 17 segments of
61 440, spread over **fifteen engines**, each with its own block of 4096 odd
numbers (one block RAM, 256 words of 16 bits) and its own block RAM of
per-prime state: the offset of the next odd multiple to strike in its block.

* **Setup.** Trial division by the primes up to 37 (residues stepped by 2) lists
  the 222 odd primes below `√(2·10^6)`. For each prime `p`, `4096 mod p` comes from
  twelve modular doublings, and the engines' first offsets follow by repeated
  modular subtraction, one engine per cycle.
* **Sieving, in lockstep.** All engines take the same prime at once (the list is
  shared): for `p ≥ 17` every cycle strikes one bit (a read–modify–write of a
  word; consecutive strikes fall in different words), and the offset for the
  next segment is where the walk leaves the block, moved on by `57344 mod p`
  (fourteen blocks) with one modular subtraction; for `p ≤ 13` every cycle
  ors a whole word with a mask from a small table (the bits `≡ ρ mod p`).
* **Summing.** Three read-back units, each serving five neighbouring engines
  (1280 words in a row), read the words back (clearing them for the next
  segment) and accumulate, with additions only, the count of primes `C`, the
  running sum of counts `R` (so `Σ w·count_w = 1280·C − R`) and the in-word
  positions (`Σ_j 2^j·popcount(z ∧ M_j)`); a combiner folds each unit into the
  total, one addition per cycle, with a short serial multiplication.

The small primes, struck from themselves, are added back at the end, with 2;
1, never struck, is taken off.
-/
namespace HDLean.Euler.P010
open HDLean.Rtl HDLean.Rtl.Build

def limit : Nat := 2000000

def reference (_ : Unit) : Nat := Id.run do
  let mut composite := Array.replicate limit false
  let mut total := 0
  for n in [2:limit] do
    if !composite[n]! then
      total := total + n
      let mut m := n * n
      while m < limit do
        composite := composite.set! m true
        m := m + n
  return total

def E : Nat := 15
def bankWords : Nat := 256
def bank : Nat := 16 * bankWords        -- 4096 odd numbers
def seg : Nat := E * bank               -- 61440
def segments : Nat := (limit / 2 + seg - 1) / seg   -- 17
def wordLimit : Nat := limit / 2 / 16   -- 62500: words at or beyond hold numbers ≥ 2·10^6
def trialPrimes : List Nat := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
def smallPrimes : List Nat := [3, 5, 7, 11, 13]
def maxCandidate : Nat := 1413          -- odd candidates up to ⌊√(2·10^6)⌋
def W : Nat := 38

/-! ## Registers -/

-- engine states
def eIdle := 0
def eLarge := 1
def eSmall := 2
def eScan := 3

/-- An engine; engines start by reading back (and so clearing) their blocks,
during the set-up. -/
hdl_record Engine where
  st : 2 := eScan
  idx : 13
  rho : 4
  raddr : 8
  pv : 1 := 0
  pm : 16
  ps : 1

/-- Three read-back units, each serving five neighbouring engines (1280 words in a row). -/
def scanners : Nat := 3
def perScanner : Nat := E / scanners
def scanWords : Nat := perScanner * bankWords
hdl_record Scanner where
  sw : 11 := 0
  sl : 1 := 0
  cc : 15
  rr : 25
  pp : 18
  zr : 16
  zv : 1 := 0
  cn : 5
  po : 7
  sv : 1 := 0

-- controller phases
def cPre := 0
def cLoad := 1
def cMark := 2
def cScanGo := 3
def cScan := 4
def cComb := 5
def cFinal := 6
def cDone := 7

hdl_record Ctrl where
  ph : 3 := cPre
  k : 8 := 0
  kr : 8 := 0
  kmax : 8 := 0
  segn : 5 := 0
  segw : 16 := 0
  ce : 3 := 0
  cs : 5 := 0
  v0 : W := 1
  sumr : W := 0
  ma : 17 := 0
  mb : W := 0
  mcnt : 5 := 0
  total : W := 0
  done : 1 := 0
  answer : W := 0

-- set-up phase
def pScan := 0
def pMod := 1
def pChain := 2
def pFin := 3

/-- The set-up, and the registered "every engine (and read-back unit) idle" and
current prime. -/
hdl_record Setup where
  pst : 2 := pScan
  m : 11 := 3
  pc : 11 := 1
  pcnt : 4 := 0
  pb : 4 := 0
  prr : 11 := 0
  kk : 8 := 0
  small : 6 := 0
  wsm : 8 := 0
  idm : 1 := 0
  ids : 1 := 0
  pkd : 22 := 0
  pkd2 : 22 := 0

/-- Engines, read-back units, controller, set-up, and the candidate's residues
modulo the trial primes. -/
abbrev State := Both (Lanes "e" E Engine) (Both (Lanes "u" scanners Scanner)
  (Both Ctrl (Both Setup (Lanes "tr" trialPrimes.length (Word 6)))))

/-- Per engine: its block (memory `2e`) and its offsets (memory `2e + 1`); then the prime list. -/
def mems : Array MemSpec :=
  ((List.range E).flatMap fun e => [ms s!"bits{e}" 8 16, ms s!"offs{e}" 8 12]).toArray ++
  #[ms "primes" 8 22]

def ctx : Ctx := solverCtx "euler10" W State
  ⟨Lanes.replicate Engine.resets, Lanes.replicate Scanner.resets, Ctrl.resets, Setup.resets,
   Lanes.ofFn fun i => ⟨.sync (3 % trialPrimes[i]!)⟩⟩ mems

/-- Popcount and position sum of a 16-bit word: the position sum is
`Σ_j 2^j · popcount(z ∧ M_j)`, `M_j` the positions with bit `j` set. -/
def wordStats (z : Sig 16) : M ctx (Sig 5 × Sig 7) := do
  let cnt ← popcount z 5
  let mut pos ← lit 7 0
  for j in [0:4] do
    let mj ← lit 16 ((List.range 16).foldl (fun acc t => if (t >>> j) % 2 == 1 then acc ||| (1 <<< t) else acc) 0)
    pos ← add pos (← shlK (← popcount (← and z mj) 7) j)
  pure (cnt, pos)

structure EngineIO where
  idle : Sig 1
  data : Sig 16
  scanValid : Sig 1
  deriving Inhabited

set_option maxRecDepth 20000 in
/-- One engine. `go`: start prime `k` (offset from its table); `scanGo`: start
reading back, a word whenever `scanEn` (at `scanAddr`, from its read-back unit).
Strikes are masks: the prime's pattern `pat` (one bit for `p ≥ 17`, bits `0, p,
2p, …` below) shifted to the offset within the word. -/
def engine (e : Nat) (go scanGo isSmall : Sig 1) (pk pk2 dk : Sig 11) (k : Sig 8) (scanEn : Sig 1) (scanAddr : Sig 8)
    (setupWrite : Sig 1) (setupAddr : Sig 8) (setupVal : Sig 12) (pat : Sig 16) (k3 : Sig 3) (wsm : Sig 8)
    (wsmLast : Sig 1) (r : Engine Sig) : M ctx (EngineIO × Engine Sig × Array (Array WritePort)) :=
    scope s!"engine {e}" do
  let st := r.st
  let idx := r.idx
  let rho := r.rho
  let raddr := r.raddr
  let pv := r.pv
  let pm := r.pm
  let ps := r.ps
  let isLarge ← eqK st eLarge
  let isSmall' ← eqK st eSmall
  let isScan ← eqK st eScan
  let offset ← readMem s!"offs{e}" 12 k        -- k is a register: the offset for prime k
  let data ← readMem s!"bits{e}" 16 raddr
  -- large primes: strike bit idx while inside the block
  let inside ← ltK idx bank
  let strike ← and1 isLarge inside
  let leave ← and1 isLarge (← not1 inside)
  let idxNext ← add idx (← zx pk 13)
  -- small primes: or word wsm (shared) with the pattern shifted by ρ; ρ steps by −16 mod p
  -- (ρ − 16) mod p for the small prime k, from a table (no adder on the prime)
  let rhoNext ← rom (← concat k3 rho) 4 fun x => match smallPrimes[x / 16]? with
    | some p => (x % 16 + 16 * p - 16) % p
    | none => 0
  let smallLast ← and1 isSmall' wsmLast
  let scanRead ← and1 isScan scanEn
  let scanLast ← and1 scanRead (← eqK scanAddr (bankWords - 1))
  -- issue: a read of one word (and, a cycle later, its write)
  let issue ← or1 strike (← or1 isSmall' scanRead)
  let addr ← ite' isLarge (← slice idx 4 8) (← ite' isScan scanAddr wsm)
  let amount ← ite' isLarge (← slice idx 0 4) rho
  let mask ← shl pat amount
  -- the pending write: or the mask in, or (reading back) clear the word
  let wdata ← ite' ps (← lit 16 0) (← or data pm)
  let writePort := port pv raddr wdata
  -- state
  let idx' ← ite' go (← zx offset 13) (← ite' strike idxNext idx)
  let rho' ← ite' go (← slice offset 0 4) (← ite' isSmall' rhoNext rho)
  let toIdle ← or1 leave (← or1 smallLast scanLast)
  let st' ← ite' go (← ite' isSmall (← lit 2 eSmall) (← lit 2 eLarge))
    (← ite' scanGo (← lit 2 eScan) (← ite' toIdle (← lit 2 eIdle) st))
  -- the offset in this engine's block of the next segment, 14 blocks further on:
  -- from where the walk leaves the block (or the last ρ), minus 57344 mod p
  let leaveOff ← slice idx 0 11                -- idx − 4096, as 4096 ≤ idx < 4096 + p
  let after ← ite' leave leaveOff (← zx rhoNext 11)
  let back ← sub (← zx after 12) (← zx dk 12)
  let newOff ← ite' (← bit back 11) (← add back (← zx pk2 12)) back
  let offWrite ← or1 leave smallLast
  let offPort := port (← or1 offWrite setupWrite) (← ite' setupWrite setupAddr k) (← ite' setupWrite setupVal newOff)
  let idle ← and1 (← eqK st eIdle) (← not1 pv)
  pure (⟨idle, data, ← and1 pv ps⟩,
    { st := st', idx := idx', rho := rho', raddr := addr, pv := issue, pm := mask, ps := isScan },
    #[#[writePort], #[offPort]])

set_option maxRecDepth 20000 in
def body : M ctx Wiring := solver "P010" State fun ⟨engines, units, c, su, trl⟩ => do
  -- controller
  let ph := c.ph
  let k := c.k
  let kr := c.kr
  let kmax := c.kmax
  let segn := c.segn
  let segw := c.segw
  let ce := c.ce
  let cs := c.cs
  let v0 := c.v0
  let sumr := c.sumr
  let ma := c.ma
  let mb := c.mb
  let mcnt := c.mcnt
  let total := c.total
  let done := c.done
  let answer := c.answer
  -- set-up
  let pst := su.pst
  let m := su.m
  let pc := su.pc
  let pcnt := su.pcnt
  let pb := su.pb
  let prr := su.prr
  let kk := su.kk
  let small := su.small
  let wsm := su.wsm
  let trs := (trl.lanes.map (·.v)).toArray
  let isPre ← eqK ph cPre
  let isLoad ← eqK ph cLoad
  let isMark ← eqK ph cMark
  let isScanGo ← eqK ph cScanGo
  let isScan ← eqK ph cScan
  let isComb ← eqK ph cComb
  -- set-up: candidates by trial division
  let isPScan ← and1 isPre (← eqK pst pScan)
  let isPMod ← and1 isPre (← eqK pst pMod)
  let isPChain ← and1 isPre (← eqK pst pChain)
  let isPFin ← and1 isPre (← eqK pst pFin)
  let mutDivs ← trialPrimes.zipIdx.mapM fun (q, i) => do
    and1 (← eqK trs[i]! 0) (← neK m q)
  let composite ← anyTree mutDivs
  let past ← ult (← lit 11 maxCandidate) m
  let foundP ← and1 isPScan (← and1 (← not1 past) (← not1 composite))
  let skipM ← and1 isPScan (← and1 (← not1 past) composite)
  let modLast ← eqK pcnt 11
  let chainLast ← eqK pb (E - 1)
  let advanceM ← or1 skipM (← and1 isPChain chainLast)
  let m' ← ite' advanceM (← addK m 2) m
  let trs' ← trialPrimes.zipIdx.mapM fun (q, i) => do
    let v ← addK trs[i]! 2
    ite' advanceM (← ite' (← geK v q) (← subK v q) v) trs[i]!
  -- 4096 mod p: twelve modular doublings
  let d2 ← shlK (← zx pc 12) 1
  let m12 ← zx m 12
  let pcDbl ← resize (← ite' (← ult d2 m12) d2 (← sub d2 m12)) 11
  let pc' ← ite' foundP (← lit 11 1) (← ite' isPMod pcDbl pc)
  let pcnt' ← ite' foundP (← lit 4 0) (← ite' isPMod (← addK pcnt 1) pcnt)
  -- the chain: offsets ((p − 1)/2 − 4096·b) mod p for engines b = 0 … 14
  let half ← shrK m 1
  let chainSub ← sub prr pc
  let chainNext ← ite' (← ult prr pc) (← add chainSub m) chainSub
  -- engine 0: from 3p (or from p, small primes); up to 2115, twelve bits
  let bank0 ← ite' (← ltK m 17) (← zx half 12) (← add (← zx half 12) (← zx m 12))
  let isB0 ← eqK pb 0
  let chainVal ← ite' isB0 bank0 (← zx chainNext 12)
  let prr' ← ite' (← and1 isPMod modLast) half (← ite' (← and1 isPChain (← not1 isB0)) chainNext prr)
  let pb' ← ite' (← and1 isPMod modLast) (← lit 4 0) (← ite' isPChain (← addK pb 1) pb)
  let kk' ← ite' (← and1 isPChain chainLast) (← addK kk 1) kk
  let small' ← ite' (← and1 isPChain (← and1 isB0 (← ltK m 17))) (← add small (← resize m 6)) small
  let pst' ← ite' foundP (← lit 2 pMod) (← ite' (← and1 isPMod modLast) (← lit 2 pChain)
    (← ite' (← and1 isPChain chainLast) (← lit 2 pScan) (← ite' (← and1 isPScan past) (← lit 2 pFin) pst)))
  let setupDone := isPFin
  -- the prime list
  -- the prime and its 57344 mod p, registered from the list (read during cLoad)
  let pkdNext ← readMem "primes" 22 k
  let pkd := su.pkd
  let pk ← slice pkd 0 11
  -- a second copy, a cycle later (the first is the block RAM's own output register),
  -- for the offset of the next segment, needed at the earliest three cycles in
  let pkd2 := su.pkd2
  let pk2 ← slice pkd2 0 11
  let dk ← slice pkd2 11 11
  -- with each prime, 57344 mod p = ((p − 1)/2 − r_14) mod p (r_14 = the last engine's offset)
  let dSub ← sub half chainNext
  let dVal ← ite' (← ult half chainNext) (← add dSub m) dSub
  let primeWrite := port (← and1 isPChain chainLast) kk (← concat dVal m)
  -- read-back units: whose turn, which word
  let us := units.lanes.toArray
  let scanState := us.map fun u => (u.sw, u.sl, u.cc, u.rr, u.pp)
  let scanPipe := us.map fun u => (u.zr, u.zv, u.cn, u.po, u.sv)
  -- engines
  let go := isLoad
  let isSmallK ← ltK k smallPrimes.length
  -- the prime's strike pattern within a word, and 16 mod p (small primes)
  let k3 ← slice k 0 3
  let smallPat ← rom k3 16 fun i => match smallPrimes[i]? with
    | some p => (List.range 16).foldl (fun acc t => if t % p == 0 then acc ||| (1 <<< t) else acc) 0
    | none => 1
  let pat ← ite' isSmallK smallPat (← lit 16 1)
  -- the small primes' word counter, shared by the engines in lockstep
  let wsmLast ← eqK wsm (bankWords - 1)
  let wsm' ← ite' go (← lit 8 0) (← addK wsm 1)
  let es := engines.lanes.toArray
  let mut engNext : Array (Engine Sig) := #[]
  let mut writes : Array (Array WritePort) := #[]
  let mut ios : Array EngineIO := #[]
  for e in [0:E] do
    let (sw, _, _, _, _) := scanState[e / perScanner]!
    let reading ← ltK sw scanWords
    let turn ← slice sw 8 3
    let scanEn ← and1 reading (← eqK turn (e % perScanner))
    let scanAddr ← slice sw 0 8
    let setupWrite ← and1 isPChain (← eqK pb e)
    let (io, r', ws) ← engine e go isScanGo isSmallK pk pk2 dk k scanEn scanAddr setupWrite kk chainVal pat k3 wsm wsmLast es[e]!
    engNext := engNext.push r'
    writes := writes ++ ws
    ios := ios.push io
  -- read-back units: a word a cycle from their engines, in order; the word's
  -- statistics a cycle after its read
  let mut scanNext : Array (Scanner Sig) := #[]
  let mut scanBusy : List (Sig 1) := []
  let mut ccs : Array (Sig 15) := #[]
  let mut rrs : Array (Sig 25) := #[]
  let mut pps : Array (Sig 18) := #[]
  for u in [0:scanners] do
    let (sw, sl, cc, rr, pp) := scanState[u]!
    let reading ← ltK sw scanWords
    -- below 2·10^6: word index segw + 1280u + sw < 62500
    let below ← ult (← add (← addK (← zx segw 17) (scanWords * u)) (← zx sw 17)) (← lit 17 wordLimit)
    let sl' ← and1 reading below
    let sw' ← ite' isScanGo (← lit 11 0) (← ite' reading (← addK sw 1) sw)
    let mut z ← lit 16 0
    let mut valid ← lit 1 0
    for i in [0:perScanner] do
      let io := ios[perScanner * u + i]!
      z ← or z (← ite' io.scanValid (← not io.data) (← lit 16 0))
      valid ← or1 valid io.scanValid
    -- three stages: the word (straight from the block RAMs into a register); its
    -- statistics; the sums (R adds the count before this word: R + C at the end)
    let (zr, zv, cn, po, sv) := scanPipe[u]!
    let zs ← ite' sl z (← lit 16 0)
    let (cnt, pos) ← wordStats zr
    let cc' ← ite' isScanGo (← lit 15 0) (← ite' sv (← add cc (← zx cn 15)) cc)
    let rr' ← ite' isScanGo (← lit 25 0) (← ite' sv (← add rr (← zx cc 25)) rr)
    let pp' ← ite' isScanGo (← lit 18 0) (← ite' sv (← add pp (← zx po 18)) pp)
    scanNext := scanNext.push
      { sw := sw', sl := sl', cc := cc', rr := rr', pp := pp', zr := zs, zv := valid, cn := cnt, po := pos, sv := zv }
    scanBusy := scanBusy ++ [reading, valid, zv, sv]
    ccs := ccs.push cc
    rrs := rrs.push rr
    pps := pps.push pp
  let allIdle ← allTree (ios.toList.map (·.idle))
  let scansIdle ← not1 (← anyTree scanBusy)
  -- marking: prime after prime, all engines in lockstep
  let lastPrime ← eq (← addK k 1) kmax
  let idm := su.idm
  let ids := su.ids
  let idm' ← and1 isMark allIdle
  let ids' ← and1 isScan (← and1 allIdle scansIdle)
  let markEnd ← and1 isMark idm
  let nextK ← addK k 1
  -- combining, one addition a cycle: per read-back unit u, with V0_u = 2·(first odd
  -- index) + 1, the sum of its primes is C·V0_u + 32·(1280·C − R) + 2·positions.
  -- Steps 0–2 add 40960·C (as 2^15·C + 2^13·C) and 2·positions; step 3 starts
  -- C·V0_u (fifteen serial steps, 4 … 18); steps 19 and 20 collect R = Q + C
  -- (its 32·R is subtracted once, at the end), and step 20 moves V0 on by 40960.
  let ccU ← pick ce ccs
  let rrU ← pick ce rrs
  let ppU ← pick ce pps
  let wideW {w : Nat} (x : Sig w) : M ctx (Sig W) := zx x W
  let isS (v : Nat) : M ctx (Sig 1) := do and1 isComb (← eqK cs v)
  let multiplying ← and1 isComb (← and1 (← geK cs 4) (← ltK cs 19))
  let operand ← or (← or (← ite' (← isS 0) (← shlK (← wideW ccU) 15) (← lit W 0))
      (← ite' (← isS 1) (← shlK (← wideW ccU) 13) (← lit W 0)))
    (← or (← ite' (← isS 2) (← shlK (← wideW ppU) 1) (← lit W 0))
      (← ite' (← and1 multiplying (← bit ma 0)) mb (← lit W 0)))
  let unitEnd ← isS 20
  let collectQ ← isS 19
  let combLast ← and1 unitEnd (← eqK ce (scanners - 1))
  let startMul ← isS 3
  let ma' ← ite' startMul (← zx ccU 17) (← ite' multiplying (← shrK ma 1) ma)
  let mb' ← ite' startMul v0 (← ite' multiplying (← shlK mb 1) mb)
  let mcnt' := mcnt
  let cs' ← ite' isComb (← ite' unitEnd (← lit 5 0) (← addK cs 1)) (← lit 5 0)
  let ce' ← ite' isComb (← ite' unitEnd (← addK ce 1) ce) (← lit 3 0)
  -- V0_0 = 32·segw + 1 at the start of a segment; + 40960 per unit
  let segStartV0 ← addK (← shlK (← wideW segw) 5) 1
  let v0' ← ite' isScanGo segStartV0 (← ite' unitEnd (← addK v0 (32 * scanWords)) v0)
  let sumr' ← ite' collectQ (← add sumr (← wideW rrU)) (← ite' unitEnd (← add sumr (← wideW ccU)) sumr)
  -- the small primes (struck from themselves) and 1 (never struck): + small − 1 + 2
  let total' ← ite' setupDone (← add total (← addK (← zx small W) 1)) (← ite' isComb (← add total operand) total)
  let lastSeg ← eqK segn (segments - 1)
  let toNext ← and1 combLast (← not1 lastSeg)
  let toFinal ← and1 combLast lastSeg
  let isFinal ← eqK ph cFinal
  let finished ← and1 isFinal (← not1 done)
  -- phases
  let ph' ← ite' setupDone (← lit 3 cLoad)
    (← ite' isLoad (← lit 3 cMark)
    (← ite' markEnd (← ite' lastPrime (← lit 3 cScanGo) (← lit 3 cLoad))
    (← ite' isScanGo (← lit 3 cScan)
    (← ite' (← and1 isScan ids) (← lit 3 cComb)
    (← ite' toNext (← lit 3 cLoad)
    (← ite' toFinal (← lit 3 cFinal)
    (← ite' finished (← lit 3 cDone) ph)))))))
  let k' ← ite' markEnd (← ite' lastPrime (← lit 8 0) nextK) k
  let kr' := kr
  let kmax' ← ite' setupDone kk kmax
  let segn' ← ite' toNext (← addK segn 1) segn
  let segw' ← ite' toNext (← addK segw (seg / 16)) segw
  -- the end: total − 32·ΣR
  let answer' ← ite' finished (← sub total (← shlK sumr 5)) answer
  let done' ← or1 done finished
  finish done answer
    ⟨Lanes.ofFn fun e => engNext.getD e default, Lanes.ofFn fun u => scanNext.getD u default,
     { ph := ph', k := k', kr := kr', kmax := kmax', segn := segn', segw := segw', ce := ce', cs := cs', v0 := v0',
       sumr := sumr', ma := ma', mb := mb', mcnt := mcnt', total := total', done := done', answer := answer' },
     { pst := pst', m := m', pc := pc', pcnt := pcnt', pb := pb', prr := prr', kk := kk', small := small',
       wsm := wsm', idm := idm', ids := ids', pkd := pkdNext, pkd2 := pkd },
     Lanes.ofFn fun i => ⟨trs'.getD i default⟩⟩
    (writes ++ #[#[primeWrite]])

def design : Except String Design := solverDesign ctx body

def problem : Problem :=
  { number := 10, title := "Summation of primes",
    idea := "A segmented odd-only sieve on fifteen lockstep engines, each with its own block RAM of 4096 odd numbers and of per-prime offsets: one strike per cycle for primes from 17, whole-word masks for 3 … 13, then a read-back that sums the primes with additions only.",
    answerWidth := W, design, reference, maxCycles := 1000000 }

end HDLean.Euler.P010
