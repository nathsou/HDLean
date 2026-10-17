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

/-- A lane walking its starts: value, steps so far, start, still active. -/
hdl_record Walker where
  x : XW
  c : CW := 0
  n : W
  act : 1 := 1

/-- Per copy, a pipeline: read address, count and start (stage 1); table entry
(the block RAM's output register), count and start (stage 2); total and start
(stage 3); the copy's best. -/
hdl_record Copy where
  v1 : 1 := 0
  raddr : TB
  c1 : CW
  n1 : W
  v2 : 1 := 0
  data : TW
  c2 : CW
  n2 : W
  v3 : 1 := 0
  t3 : CW
  n3 : W
  bc : CW := 0
  bn : W := 0

/-- The table builder, then the final comparison. -/
hdl_record Glob where
  built : 1 := 0
  y : (TB + 1) := 1
  xb : XW := 0
  cb : CW := 0
  bst : 2 := 0
  done : 1 := 0
  answer : W := 0

abbrev State := Both (Lanes "l" L Walker) (Both (Lanes "k" copies Copy) Glob)

def mems : Array MemSpec := ((List.range copies).map fun k => ms s!"tail{k}" TB TW).toArray

def ctx : Ctx := solverCtx "euler14" W State
  ⟨Lanes.ofFn fun l => { Walker.resets with x := .sync (lanes[l]!).1, n := .sync (lanes[l]!).1 },
   Lanes.replicate Copy.resets, Glob.resets⟩ mems

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

structure Req where
  req : Sig 1
  addr : Sig TB
  c : Sig CW
  n : Sig W
  deriving Inhabited

def body : M ctx Wiring := solver "P014" State fun ⟨walkers, cps, g⟩ => do
  let ws := walkers.lanes.toArray
  let cs := cps.lanes.toArray
  let built := g.built
  let y := g.y
  let xb := g.xb
  let cb := g.cb
  let bst := g.bst
  let done := g.done
  let answer := g.answer
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
  let data0 := cs[0]!.data
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
  let mut laneOut : Array Req := #[]
  let mut acts : List (Sig 1) := []
  for w in ws do
    let x := w.x
    let c := w.c
    let n := w.n
    let act := w.act
    let req ← and1 built (← and1 act (← small x))
    laneOut := laneOut.push ⟨req, ← slice x 0 TB, c, n⟩
    acts := acts ++ [act]
  -- arbiters: the lowest requesting lane of each copy is granted
  let mut granted : Array (Sig 1) := Array.replicate L ⟨0⟩
  let mut copyNext : Array (Copy Sig) := #[]
  let mut writes : Array (Array WritePort) := #[]
  let mut busy : List (Sig 1) := []
  let mut bcs : Array (Sig CW) := #[]
  let mut bns : Array (Sig W) := #[]
  for k in [0:copies] do
    let cp := cs[k]!
    let v1 := cp.v1
    let raddr := cp.raddr
    let c1 := cp.c1
    let n1 := cp.n1
    let v2 := cp.v2
    let data := cp.data
    let c2 := cp.c2
    let n2 := cp.n2
    let v3 := cp.v3
    let t3 := cp.t3
    let n3 := cp.n3
    let bc := cp.bc
    let bn := cp.bn
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
    let entry ← readMem s!"tail{k}" TW raddr
    let total ← add c2 (← zx data CW)
    let better ← and1 v3 (← ult bc t3)
    let bc' ← ite' better t3 bc
    let bn' ← ite' better n3 bn
    let cp' : Copy Sig :=
      { v1 := taken, raddr := addr, c1 := cSel, n1 := nSel, v2 := v1, data := entry, c2 := c1, n2 := n1,
        v3 := v2, t3 := total, n3 := n2, bc := bc', bn := bn' }
    copyNext := copyNext.push cp'
    writes := writes.push #[port bwrite yAddr bval]
    busy := busy ++ [v1, v2, v3]
    bcs := bcs.push bc
    bns := bns.push bn
  -- lanes: step, or move on to the next start once granted
  let mut laneNext : Array (Walker Sig) := #[]
  for ((n0, stride, last), l) in lanes.zipIdx do
    let x := ws[l]!.x
    let c := ws[l]!.c
    let n := ws[l]!.n
    let act := ws[l]!.act
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
    laneNext := laneNext.push { x := x', c := c', n := n', act := act' }
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
  finish done answer
    ⟨Lanes.ofFn fun l => laneNext.getD l default, Lanes.ofFn fun k => copyNext.getD k default,
     { built := built', y := y', xb := xb', cb := cb', bst := bst', done := done', answer := answer' }⟩ writes

def design : Except String Design := solverDesign ctx body

def problem : Problem :=
  { number := 14, title := "Longest Collatz sequence",
    idea := "24 lanes, two Collatz steps per cycle each (x = 4q + r becomes q, 3q + 1, 3q + 2 or 9q + 8: one addition of shifted copies), each walking until its value drops below 2048 and handing the rest to a table built first in block RAM; only the 333 333 starts not dominated by a larger start's chain.",
    answerWidth := W, design, reference, maxCycles := 2000000 }

end HDLean.Euler.P014
