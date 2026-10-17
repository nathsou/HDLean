import Designs.Euler.Kit

/-!
# Problem 14: longest Collatz sequence

The start below one million with the longest Collatz chain.

**Fewer starts.** A start `n` cannot win if some larger start below one million
passes through it: `2n` does for every `n < 500 000`, and for `n < 750 000` not
divisible by 3 so does `(4n − 1)/3` (when `n ≡ 1 mod 3`, an odd number whose
`3x + 1` is `4n`) or `(4n − 2)/3` (when `n ≡ 2 mod 3`: an even number halving to
the odd `(2n − 1)/3`, whose `3x + 1` is `2n`). That leaves the multiples of 3 in
`[500 000, 750 000)` and every start in `[750 000, 1 000 000)`: 333 333 starts.

**Two steps per cycle.** Writing `x = 4q + r`, two steps of the shortcut map
(`x/2`, `(3x + 1)/2`) give `q`, `3q + 1`, `3q + 2` or `9q + 8`, that is
`(x + B)/4` with `B` = `0`, `2x + 1`, `2x + 2` or `8x + 5`: one addition, as the
constants fill bits of the shifted copy of `x` that are known to be zero. The chain length grows by 2, 3, 3 or 4 Collatz steps.

**Memoised tails.** A table of the chain lengths below 2048 is built first, in
block RAM, by a small engine that walks each `y` only until it drops below `y`
and adds the table entry found there. A lane walks its start only until it drops
below 2048 (about 21 cycles on average), then reads the rest of the chain from
the table.

**24 lanes.** Six lanes take the multiples of 3, eighteen take the rest,
each walking its own arithmetic progression of starts. The table is replicated
four times (one read port each), every copy serving six lanes through a
fixed-priority arbiter: a granted lane hands its start, its step count and its
table address to the copy's pipeline and moves on to its next start at once. The
pipeline adds the tail and keeps the copy's best; at the end the four bests are
compared.
-/
namespace HDLean.Euler.P014
open HDLean.Rtl HDLean.Rtl.Build

def collatzLength (n : Nat) : Nat := Id.run do
  let mut x := n
  let mut len := 1
  for _ in [:2000] do
    if x == 1 then return len
    x := if x % 2 == 0 then x / 2 else 3 * x + 1
    len := len + 1
  return len

/-- Every start below one million. -/
def reference (_ : Unit) : Nat := Id.run do
  let mut best := 0
  let mut arg := 0
  for n in [1:1000000] do
    let l := collatzLength n
    if l > best then
      best := l
      arg := n
  return arg

def XW : Nat := 36
def CW : Nat := 10
def W : Nat := 20
/-- The table covers `0 … 2^TB − 1`. -/
def TB : Nat := 11
def TW : Nat := 8
def copies : Nat := 4

/-- Lanes: first start, stride, last start. -/
def groupA : Nat := 6
def groupB : Nat := 18
def lanes : List (Nat × Nat × Nat) :=
  ((List.range groupA).map fun j => (500001 + 3 * j, 3 * groupA, 749997)) ++
  ((List.range groupB).map fun j => (750000 + j, groupB, 999999))
def L : Nat := lanes.length

/-- The last start of a lane. -/
def lastStart (n0 stride last : Nat) : Nat := n0 + (last - n0) / stride * stride

def laneRegs : List RegSpec :=
  lanes.zipIdx.flatMap fun ((n0, _, _), l) =>
    [rs s!"x{l}" XW (.sync n0), rs s!"c{l}" CW (.sync 0), rs s!"n{l}" W (.sync n0), rs s!"act{l}" 1 (.sync 1)]
def laneBase (l : Nat) : Nat := 4 * l

/-- Per copy, a pipeline: read address, count and start (stage 1); table entry
(the block RAM's output register), count and start (stage 2); total and start
(stage 3); the copy's best. -/
def copyRegs : List RegSpec :=
  (List.range copies).flatMap fun k =>
    [rs s!"v1_{k}" 1 (.sync 0), rs s!"raddr{k}" TB, rs s!"c1_{k}" CW, rs s!"n1_{k}" W,
     rs s!"v2_{k}" 1 (.sync 0), rs s!"data{k}" TW, rs s!"c2_{k}" CW, rs s!"n2_{k}" W,
     rs s!"v3_{k}" 1 (.sync 0), rs s!"t3_{k}" CW, rs s!"n3_{k}" W,
     rs s!"bc{k}" CW (.sync 0), rs s!"bn{k}" W (.sync 0)]
def copyBase (k : Nat) : Nat := 4 * L + 13 * k

/-- The table builder, then the final comparison. -/
def gBase : Nat := 4 * L + 13 * copies
def globalRegs : List RegSpec :=
  [rs "built" 1 (.sync 0), rs "y" (TB + 1) (.sync 1), rs "xb" XW (.sync 0), rs "cb" CW (.sync 0),
   rs "bst" 2 (.sync 0), rs "done" 1 (.sync 0), rs "answer" W (.sync 0)]

def regs : Array RegSpec := (laneRegs ++ copyRegs ++ globalRegs).toArray

def mems : Array MemSpec := ((List.range copies).map fun k => ms s!"tail{k}" TB TW).toArray

def ctx : Ctx := solverCtx "euler14" W regs mems

/-- Two shortcut steps: `x ↦ (x + B)/4` with `B` = `0`, `2x|1`, `2x|2` or `8x|5`
(the constant fills bits of the shifted copy that are known to be zero), and the
Collatz steps taken. -/
def step (x : Sig XW) : M ctx (Sig XW × Sig CW) := do
  let xw ← zx x (XW + 2)
  let r ← slice x 0 2
  let r0 ← eqK r 0
  let r1 ← eqK r 1
  let r3 ← eqK r 3
  let twoX ← or (← shlK xw 1) (← ite' r1 (← lit (XW + 2) 1) (← lit (XW + 2) 2))
  let eightX ← or (← shlK xw 3) (← lit (XW + 2) 5)
  let b ← ite' r0 (← lit (XW + 2) 0) (← ite' r3 eightX twoX)
  let x' ← slice (← add xw b) 2 XW
  let inc ← ite' r0 (← lit CW 2) (← ite' r3 (← lit CW 4) (← lit CW 3))
  pure (x', inc)

/-- Below the table's range. -/
def small (x : Sig XW) : M ctx (Sig 1) := do eqK (← shrK x TB) 0

-- builder states
def bWalk := 0
def bWait := 1
def bWrite := 2

structure Lane where
  req : Sig 1
  addr : Sig TB
  c : Sig CW
  n : Sig W
  deriving Inhabited

def body : M ctx Wiring := do
  let built ← rd gBase 1
  let y ← rd (gBase + 1) (TB + 1)
  let xb ← rd (gBase + 2) XW
  let cb ← rd (gBase + 3) CW
  let bst ← rd (gBase + 4) 2
  let done ← rd (gBase + 5) 1
  let answer ← rd (gBase + 6) W
  -- the builder: walk y until it drops below y, then add the table entry there
  let isWalk ← eqK bst bWalk
  let isWait ← eqK bst bWait
  let isWrite ← eqK bst bWrite
  let building ← not1 built
  let first ← ltK y 3                      -- T[1] = 0, T[2] = 1
  let below ← ult xb (← zx y XW)
  let issue ← and1 building (← and1 isWalk (← and1 (← not1 first) below))
  let direct ← and1 building (← and1 isWalk first)
  let walk ← and1 building (← and1 isWalk (← and1 (← not1 first) (← not1 below)))
  let data0 ← rd (copyBase 0 + 5) TW
  let bval ← ite' direct (← resize (← subK y 1) TW) (← resize (← add cb (← zx data0 CW)) TW)
  let bwrite ← or1 direct (← and1 building isWrite)
  let yNext ← addK y 1
  let lastY ← eqK y ((1 <<< TB) - 1)
  let (xbs, binc) ← step xb
  let xb' ← ite' bwrite (← zx yNext XW) (← ite' walk xbs xb)
  let cb' ← ite' bwrite (← lit CW 0) (← ite' walk (← add cb binc) cb)
  let y' ← ite' bwrite yNext y
  let bst' ← ite' issue (← lit 2 bWait) (← ite' isWait (← lit 2 bWrite) (← ite' isWrite (← lit 2 bWalk) bst))
  let built' ← or1 built (← and1 bwrite lastY)
  let yAddr ← slice y 0 TB
  -- lanes: walk until the value drops below the table's range, then request
  let mut laneOut : Array Lane := #[]
  let mut acts : List (Sig 1) := []
  for (_, l) in lanes.zipIdx do
    let x ← rd (laneBase l) XW
    let c ← rd (laneBase l + 1) CW
    let n ← rd (laneBase l + 2) W
    let act ← rd (laneBase l + 3) 1
    let req ← and1 built (← and1 act (← small x))
    laneOut := laneOut.push ⟨req, ← slice x 0 TB, c, n⟩
    acts := acts ++ [act]
  -- arbiters: the lowest requesting lane of each copy is granted
  let mut granted : Array (Sig 1) := Array.replicate L ⟨0⟩
  let mut copyNexts : Array Nat := #[]
  let mut writes : Array (Array WritePort) := #[]
  let mut busy : List (Sig 1) := []
  let mut bcs : Array (Sig CW) := #[]
  let mut bns : Array (Sig W) := #[]
  for k in [0:copies] do
    let v1 ← rd (copyBase k) 1
    let raddr ← rd (copyBase k + 1) TB
    let c1 ← rd (copyBase k + 2) CW
    let n1 ← rd (copyBase k + 3) W
    let v2 ← rd (copyBase k + 4) 1
    let data ← rd (copyBase k + 5) TW
    let c2 ← rd (copyBase k + 6) CW
    let n2 ← rd (copyBase k + 7) W
    let v3 ← rd (copyBase k + 8) 1
    let t3 ← rd (copyBase k + 9) CW
    let n3 ← rd (copyBase k + 10) W
    let bc ← rd (copyBase k + 11) CW
    let bn ← rd (copyBase k + 12) W
    let mut taken ← lit 1 0
    let mut addr := raddr
    let mut cSel := c1
    let mut nSel := n1
    for l in [0:L] do
      if l % copies == k then
        let ln := laneOut[l]!
        let g ← and1 ln.req (← not1 taken)
        granted := granted.set! l g
        addr ← ite' g ln.addr addr
        cSel ← ite' g ln.c cSel
        nSel ← ite' g ln.n nSel
        taken ← or1 taken ln.req
    if k == 0 then
      addr ← ite' issue (← slice xb 0 TB) addr
    let entry ← memRead k TW raddr
    let total ← add c2 (← zx data CW)
    let better ← and1 v3 (← ult bc t3)
    let bc' ← ite' better t3 bc
    let bn' ← ite' better n3 bn
    copyNexts := copyNexts ++ #[taken.ref, addr.ref, cSel.ref, nSel.ref, v1.ref, entry.ref, c1.ref, n1.ref,
      v2.ref, total.ref, n2.ref, bc'.ref, bn'.ref]
    writes := writes.push #[port bwrite yAddr bval]
    busy := busy ++ [v1, v2, v3]
    bcs := bcs.push bc
    bns := bns.push bn
  -- lanes: step, or move on to the next start once granted
  let mut laneNexts : Array Nat := #[]
  for ((n0, stride, last), l) in lanes.zipIdx do
    let x ← rd (laneBase l) XW
    let c ← rd (laneBase l + 1) CW
    let n ← rd (laneBase l + 2) W
    let act ← rd (laneBase l + 3) 1
    let g := granted[l]!
    let stepping ← and1 act (← not1 (← small x))
    let more ← neK n (lastStart n0 stride last)
    let reload ← and1 g more
    let nNext ← addK n stride
    let (xs, inc) ← step x
    let x' ← ite' reload (← zx nNext XW) (← ite' stepping xs x)
    let c' ← ite' reload (← lit CW 0) (← ite' stepping (← add c inc) c)
    let n' ← ite' reload nNext n
    let act' ← and1 act (← or1 (← not1 g) more)
    laneNexts := laneNexts ++ #[x'.ref, c'.ref, n'.ref, act'.ref]
  -- the end: every lane finished and every pipeline drained; the best of the copies
  let finished ← and1 built (← and1 (← not1 (← anyTree (acts ++ busy))) (← not1 done))
  let mut best := bcs[0]!
  let mut arg := bns[0]!
  for k in [1:copies] do
    let b ← ult best bcs[k]!
    best ← ite' b bcs[k]! best
    arg ← ite' b bns[k]! arg
  let answer' ← ite' finished arg answer
  let done' ← or1 done finished
  pure (solverWiring ⟨done, answer.ref, laneNexts ++ copyNexts ++
    #[built'.ref, y'.ref, xb'.ref, cb'.ref, bst'.ref, done'.ref, answer'.ref], writes⟩)

def design : Design := single ctx body

def problem : Problem :=
  { number := 14, title := "Longest Collatz sequence",
    idea := "24 lanes, two Collatz steps per cycle each (x = 4q + r becomes q, 3q + 1, 3q + 2 or 9q + 8: one addition of shifted copies), each walking until its value drops below 2048 and handing the rest to a table built first in block RAM; only the 333 333 starts not dominated by a larger start's chain.",
    answerWidth := W, design, reference, maxCycles := 2000000 }

end HDLean.Euler.P014
