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

def engineRegs (e : Nat) : List RegSpec :=
  -- engines start by reading back (and so clearing) their blocks, during the set-up
  [rs s!"st{e}" 2 (.sync eScan), rs s!"idx{e}" 13, rs s!"rho{e}" 4, rs s!"raddr{e}" 8,
   rs s!"pv{e}" 1 (.sync 0), rs s!"pm{e}" 16, rs s!"ps{e}" 1]
def eSize : Nat := 7
def eBase (e : Nat) : Nat := eSize * e

/-- Three read-back units, each serving five neighbouring engines (1280 words in a row). -/
def scanners : Nat := 3
def perScanner : Nat := E / scanners
def scanWords : Nat := perScanner * bankWords
def scanRegs (u : Nat) : List RegSpec :=
  [rs s!"sw{u}" 11 (.sync 0), rs s!"sl{u}" 1 (.sync 0), rs s!"cc{u}" 15, rs s!"rr{u}" 25, rs s!"pp{u}" 18,
   rs s!"zr{u}" 16, rs s!"zv{u}" 1 (.sync 0), rs s!"cn{u}" 5, rs s!"po{u}" 7, rs s!"sv{u}" 1 (.sync 0)]
def uSize : Nat := 10
def uBase (u : Nat) : Nat := eSize * E + uSize * u

-- controller phases
def cPre := 0
def cLoad := 1
def cMark := 2
def cScanGo := 3
def cScan := 4
def cComb := 5
def cFinal := 6
def cDone := 7

def cBase : Nat := eSize * E + uSize * scanners
def ctrlRegs : List RegSpec :=
  [rs "ph" 3 (.sync cPre), rs "k" 8 (.sync 0), rs "kr" 8 (.sync 0), rs "kmax" 8 (.sync 0),
   rs "segn" 5 (.sync 0), rs "segw" 16 (.sync 0), rs "ce" 3 (.sync 0),
   rs "cs" 5 (.sync 0), rs "v0" W (.sync 1), rs "sumr" W (.sync 0),
   rs "ma" 17 (.sync 0), rs "mb" W (.sync 0), rs "mcnt" 5 (.sync 0),
   rs "total" W (.sync 0), rs "done" 1 (.sync 0), rs "answer" W (.sync 0)]
def cSize : Nat := 16

-- set-up phase
def pScan := 0
def pMod := 1
def pChain := 2
def pFin := 3

def sBase : Nat := cBase + cSize
def setupRegs : List RegSpec :=
  [rs "pst" 2 (.sync pScan), rs "m" 11 (.sync 3), rs "pc" 11 (.sync 1), rs "pcnt" 4 (.sync 0),
   rs "pb" 4 (.sync 0), rs "prr" 11 (.sync 0), rs "kk" 8 (.sync 0), rs "small" 6 (.sync 0),
   rs "wsm" 8 (.sync 0)] ++
  trialPrimes.map (fun q => rs s!"tr{q}" 6 (.sync (3 % q))) ++
  -- every engine (and read-back unit) idle, registered
  [rs "idm" 1 (.sync 0), rs "ids" 1 (.sync 0), rs "pkd" 22 (.sync 0), rs "pkd2" 22 (.sync 0)]
def sSize : Nat := 13 + trialPrimes.length

def regs : Array RegSpec :=
  ((List.range E).flatMap engineRegs ++ (List.range scanners).flatMap scanRegs ++ ctrlRegs ++ setupRegs).toArray

/-- Per engine: its block (memory `2e`) and its offsets (memory `2e + 1`); then the prime list. -/
def mems : Array MemSpec :=
  ((List.range E).flatMap fun e => [ms s!"bits{e}" 8 16, ms s!"offs{e}" 8 12]).toArray ++
  #[ms "primes" 8 22]

def ctx : Ctx := solverCtx "euler10" W regs mems

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
    (wsmLast : Sig 1) : M ctx (EngineIO × Array Nat × Array (Array WritePort)) := do
  let b := eBase e
  let st ← rd b 2
  let idx ← rd (b + 1) 13
  let rho ← rd (b + 2) 4
  let raddr ← rd (b + 3) 8
  let pv ← rd (b + 4) 1
  let pm ← rd (b + 5) 16
  let ps ← rd (b + 6) 1
  let isLarge ← eqK st eLarge
  let isSmall' ← eqK st eSmall
  let isScan ← eqK st eScan
  let offset ← memRead (2 * e + 1) 12 k        -- k is a register: the offset for prime k
  let data ← memRead (2 * e) 16 raddr
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
    #[st'.ref, idx'.ref, rho'.ref, addr.ref, issue.ref, mask.ref, isScan.ref],
    #[#[writePort], #[offPort]])

set_option maxRecDepth 20000 in
def body : M ctx Wiring := do
  -- controller
  let ph ← rd cBase 3
  let k ← rd (cBase + 1) 8
  let kr ← rd (cBase + 2) 8
  let kmax ← rd (cBase + 3) 8
  let segn ← rd (cBase + 4) 5
  let segw ← rd (cBase + 5) 16
  let ce ← rd (cBase + 6) 3
  let cs ← rd (cBase + 7) 5
  let v0 ← rd (cBase + 8) W
  let sumr ← rd (cBase + 9) W
  let ma ← rd (cBase + 10) 17
  let mb ← rd (cBase + 11) W
  let mcnt ← rd (cBase + 12) 5
  let total ← rd (cBase + 13) W
  let done ← rd (cBase + 14) 1
  let answer ← rd (cBase + 15) W
  -- set-up
  let pst ← rd sBase 2
  let m ← rd (sBase + 1) 11
  let pc ← rd (sBase + 2) 11
  let pcnt ← rd (sBase + 3) 4
  let pb ← rd (sBase + 4) 4
  let prr ← rd (sBase + 5) 11
  let kk ← rd (sBase + 6) 8
  let small ← rd (sBase + 7) 6
  let wsm ← rd (sBase + 8) 8
  let trs ← trialPrimes.zipIdx.mapM fun (_, i) => rd (sBase + 9 + i) 6
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
  let pkdNext ← memRead (2 * E) 22 k
  let pkd ← rd (sBase + 11 + trialPrimes.length) 22
  let pk ← slice pkd 0 11
  -- a second copy, a cycle later (the first is the block RAM's own output register),
  -- for the offset of the next segment, needed at the earliest three cycles in
  let pkd2 ← rd (sBase + 12 + trialPrimes.length) 22
  let pk2 ← slice pkd2 0 11
  let dk ← slice pkd2 11 11
  -- with each prime, 57344 mod p = ((p − 1)/2 − r_14) mod p (r_14 = the last engine's offset)
  let dSub ← sub half chainNext
  let dVal ← ite' (← ult half chainNext) (← add dSub m) dSub
  let primeWrite := port (← and1 isPChain chainLast) kk (← concat dVal m)
  -- read-back units: whose turn, which word
  let scanState ← (List.range scanners).mapM fun u => do
    pure (← rd (uBase u) 11, ← rd (uBase u + 1) 1, ← rd (uBase u + 2) 15, ← rd (uBase u + 3) 25, ← rd (uBase u + 4) 18)
  let scanPipe ← (List.range scanners).mapM fun u => do
    pure (← rd (uBase u + 5) 16, ← rd (uBase u + 6) 1, ← rd (uBase u + 7) 5, ← rd (uBase u + 8) 7, ← rd (uBase u + 9) 1)
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
  let mut nexts : Array Nat := #[]
  let mut writes : Array (Array WritePort) := #[]
  let mut ios : Array EngineIO := #[]
  for e in [0:E] do
    let (sw, _, _, _, _) := scanState[e / perScanner]!
    let reading ← ltK sw scanWords
    let turn ← slice sw 8 3
    let scanEn ← and1 reading (← eqK turn (e % perScanner))
    let scanAddr ← slice sw 0 8
    let setupWrite ← and1 isPChain (← eqK pb e)
    let (io, ns, ws) ← engine e go isScanGo isSmallK pk pk2 dk k scanEn scanAddr setupWrite kk chainVal pat k3 wsm wsmLast
    nexts := nexts ++ ns
    writes := writes ++ ws
    ios := ios.push io
  -- read-back units: a word a cycle from their engines, in order; the word's
  -- statistics a cycle after its read
  let mut scanNexts : Array Nat := #[]
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
    scanNexts := scanNexts ++ #[sw'.ref, sl'.ref, cc'.ref, rr'.ref, pp'.ref, zs.ref, valid.ref, cnt.ref, pos.ref, zv.ref]
    scanBusy := scanBusy ++ [reading, valid, zv, sv]
    ccs := ccs.push cc
    rrs := rrs.push rr
    pps := pps.push pp
  let allIdle ← allTree (ios.toList.map (·.idle))
  let scansIdle ← not1 (← anyTree scanBusy)
  -- marking: prime after prime, all engines in lockstep
  let lastPrime ← eq (← addK k 1) kmax
  let idm ← rd (sBase + 9 + trialPrimes.length) 1
  let ids ← rd (sBase + 10 + trialPrimes.length) 1
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
  pure (solverWiring ⟨done, answer.ref,
    nexts ++ scanNexts ++ #[ph'.ref, k'.ref, kr'.ref, kmax'.ref, segn'.ref, segw'.ref, ce'.ref, cs'.ref, v0'.ref,
      sumr'.ref, ma'.ref, mb'.ref, mcnt'.ref, total'.ref, done'.ref, answer'.ref] ++
    #[pst'.ref, m'.ref, pc'.ref, pcnt'.ref, pb'.ref, prr'.ref, kk'.ref, small'.ref, wsm'.ref] ++
    (trs'.map (·.ref)).toArray ++ #[idm'.ref, ids'.ref, pkdNext.ref, pkd.ref],
    writes ++ #[#[primeWrite]]⟩)

def design : Design := single ctx body

def problem : Problem :=
  { number := 10, title := "Summation of primes",
    idea := "A segmented odd-only sieve on fifteen lockstep engines, each with its own block RAM of 4096 odd numbers and of per-prime offsets: one strike per cycle for primes from 17, whole-word masks for 3 … 13, then a read-back that sums the primes with additions only.",
    answerWidth := W, design, reference, maxCycles := 1000000 }

end HDLean.Euler.P010
