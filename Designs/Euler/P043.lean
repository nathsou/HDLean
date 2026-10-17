import Designs.Euler.Kit

/-!
# Problem 43: sub-string divisibility

The sum of the 0–9 pandigital numbers `d1 d2 … d10` in which `d2d3d4` is
divisible by 2, `d3d4d5` by 3, `d4d5d6` by 5, `d5d6d7` by 7, `d6d7d8` by 11,
`d7d8d9` by 13 and `d8d9d10` by 17.

A depth-first search from the right, one digit per cycle, pruned as soon as a
three-digit window fails. Each level keeps the residue `−(10a + b) mod p` that
the window `c a b` needs from `100c` (computed from small tables when the search
moves down or up), so testing a candidate is one table lookup and a compare. The digit registers are the search stack (backtracking
resumes after the digit that was there), a ten-bit mask holds the digits in use.
Ten lanes take the ten choices of `d10`. A completed number is turned into binary
in ten steps (`v ← 10v + d`) and added to the lane's sum; the lanes' sums are
added at the end.
-/
namespace HDLean.Euler.P043
open HDLean.Rtl HDLean.Rtl.Build

def reference (_ : Unit) : Nat := Id.run do
  let primes := [2, 3, 5, 7, 11, 13, 17]
  let mut total := 0
  -- digits from the right, as a list of partial suffixes
  let mut suffixes : List (List Nat) := (List.range 10).map fun d => [d]
  for _ in [:9] do
    let mut next := []
    for suf in suffixes do
      for c in [0:10] do
        if !suf.contains c then
          let s := c :: suf
          let pos := 11 - s.length   -- the position of c (1 … 10)
          let ok := if pos ≤ 7 ∧ pos ≥ 2 then
              (100 * c + 10 * s[1]! + s[2]!) % primes[pos - 2]! == 0
            else if pos == 8 then (100 * c + 10 * s[1]! + s[2]!) % 17 == 0
            else true
          if ok then next := s :: next
    suffixes := next
  for s in suffixes do
    total := total + s.foldl (fun acc d => 10 * acc + d) 0
  return total

def W : Nat := 36
def VW : Nat := 36
def lanes : Nat := 10

/-- The prime for the window starting at position `i` (2 … 8). -/
def primeAt (i : Nat) : Nat := match i with
  | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 7 | 6 => 11 | 7 => 13 | 8 => 17 | _ => 1

-- lane modes
def mSearch := 0
def mConv := 1
def mAdd := 2
def mDone := 3

/-- Per lane: digits d1 … d9 (d10 is the lane's), the mask, the position being
chosen, the candidate, then the conversion. -/
def laneRegs (l : Nat) : List RegSpec :=
  (List.range 9).map (fun k => rs s!"d{k + 1}_{l}" 4 (.sync 0)) ++
  [rs s!"used{l}" 10 (.sync (1 <<< l)), rs s!"pos{l}" 4 (.sync 9), rs s!"cand{l}" 4 (.sync 0),
   rs s!"mode{l}" 2 (.sync mSearch), rs s!"k{l}" 4 (.sync 0), rs s!"v{l}" VW (.sync 0), rs s!"tot{l}" W (.sync 0),
   -- d(pos+1), and the residue the window at pos needs from 100·cand (pos = 9: none)
   rs s!"wa{l}" 4 (.sync l), rs s!"need{l}" 5 (.sync 0), rs s!"win{l}" 1 (.sync 0)]
def laneSize : Nat := 19
def laneBase (l : Nat) : Nat := laneSize * l

def gBase : Nat := laneSize * lanes
def regs : Array RegSpec :=
  ((List.range lanes).flatMap laneRegs ++
   [rs "scan" 4 (.sync 0), rs "sum" W (.sync 0), rs "done" 1 (.sync 0), rs "answer" W (.sync 0)]).toArray

def ctx : Ctx := solverCtx "euler43" W regs

/-- The residue `100·c` must have, modulo the prime of the window at position
`i`, for the window `c a b` to be divisible: `−(10a + b) mod p`. -/
def needOf (i : Sig 4) (a b : Sig 4) : M ctx (Sig 5) := do
  let p ← rom i 5 primeAt
  let r10 ← rom (← concat i a) 5 fun x => (10 * (x % 16)) % primeAt (x / 16)
  let r1 ← rom (← concat i b) 5 fun x => (x % 16) % primeAt (x / 16)
  let s ← add (← zx r10 6) (← zx r1 6)
  let s1 ← slice (← ite' (← ult s (← zx p 6)) s (← sub s (← zx p 6))) 0 5
  ite' (← eqK s1 0) (← lit 5 0) (← sub p s1)

/-- Whether position `i` starts a window (2 … 8). -/
def windowAt (i : Sig 4) : M ctx (Sig 1) := do and1 (← geK i 2) (← ltK i 9)

structure LaneIO where
  done : Sig 1
  tot : Sig W
  deriving Inhabited

set_option maxRecDepth 20000 in
def lane (l : Nat) : M ctx (LaneIO × Array Nat) := do
  let b := laneBase l
  let ds ← (List.range 9).mapM fun k => rd (b + k) 4
  let used ← rd (b + 9) 10
  let pos ← rd (b + 10) 4
  let cand ← rd (b + 11) 4
  let mode ← rd (b + 12) 2
  let k ← rd (b + 13) 4
  let v ← rd (b + 14) VW
  let tot ← rd (b + 15) W
  let wa ← rd (b + 16) 4
  let need ← rd (b + 17) 5
  let win ← rd (b + 18) 1
  let d10 ← lit 4 l
  let digits := ds ++ [d10]           -- digits[i - 1] = d_i
  let digitAt (i : Sig 4) : M ctx (Sig 4) := do
    -- d_i for i = 1 … 10 (index i − 1)
    pick (← subK i 1) digits.toArray
  let isSearch ← eqK mode mSearch
  let isConv ← eqK mode mConv
  let isAdd ← eqK mode mAdd
  -- the window c·100 + a·10 + b at position pos: 100·cand must have residue need
  let rc ← rom (← concat pos cand) 5 fun x => (100 * (x % 16)) % primeAt (x / 16)
  let divOk ← or1 (← not1 win) (← eq rc need)
  let candBit ← bit (← lshr used (← zx cand 10)) 0
  let exhausted ← eqK cand 10
  let ok ← and1 (← not1 exhausted) (← and1 (← not1 candBit) divOk)
  let atOne ← eqK pos 1
  let atTop ← eqK pos 9
  -- search moves
  let backtrack ← and1 isSearch exhausted
  let finishLane ← and1 backtrack atTop
  let up ← and1 backtrack (← not1 atTop)
  let place ← and1 isSearch ok
  let descend ← and1 place (← not1 atOne)
  let complete ← and1 place atOne
  let skipC ← and1 isSearch (← and1 (← not1 exhausted) (← not1 ok))
  -- the digit to resume after when going up: d(pos+1)
  let prev := wa
  let prevMask ← shl (← lit 10 1) (← zx prev 10)
  let candMask ← shl (← lit 10 1) (← zx cand 10)
  let used' ← ite' descend (← or used candMask) (← ite' up (← and used (← not prevMask)) used)
  let pos' ← ite' descend (← subK pos 1) (← ite' up (← addK pos 1) pos)
  let cand' ← ite' descend (← lit 4 0) (← ite' up (← addK prev 1)
    (← ite' (← or1 skipC (← and1 isAdd (← lit 1 1))) (← addK cand 1) cand))
  -- digit registers: d_pos ← cand when placed
  let mut ds' : List (Sig 4) := []
  for i in [1:10] do
    let here ← and1 place (← eqK pos i)
    ds' := ds' ++ [← ite' here cand ds[i - 1]!]
  -- the window state of the next position: going down, a = cand and b = d(pos+1);
  -- going up, a = d(pos+2) and b = d(pos+3)
  let posDn ← subK pos 1
  let posUp ← addK pos 1
  let a2 ← digitAt (← addK pos 2)
  let a3 ← digitAt (← addK pos 3)
  let wa' ← ite' descend cand (← ite' up a2 wa)
  -- (one table set per lane: going up needs `exhausted`, going down excludes it)
  let nNeed ← needOf (← ite' exhausted posUp posDn) (← ite' exhausted a2 cand) (← ite' exhausted a3 wa)
  let nWin ← windowAt (← ite' exhausted posUp posDn)
  let moved ← or1 descend up
  let need' ← ite' moved nNeed need
  let win' ← ite' moved nWin win
  -- conversion: v ← 10v + d_k for k = 1 … 10, then add
  let dk ← digitAt k
  let ten ← add (← shlK v 3) (← shlK v 1)
  let v' ← ite' complete (← lit VW 0) (← ite' isConv (← add ten (← zx dk VW)) v)
  let k' ← ite' complete (← lit 4 1) (← ite' isConv (← addK k 1) k)
  let convLast ← eqK k 10
  let tot' ← ite' isAdd (← add tot v) tot
  let mode' ← ite' complete (← lit 2 mConv) (← ite' (← and1 isConv convLast) (← lit 2 mAdd)
    (← ite' isAdd (← lit 2 mSearch) (← ite' finishLane (← lit 2 mDone) mode)))
  pure (⟨← eqK mode mDone, tot⟩,
    (ds'.map (·.ref)).toArray ++ #[used'.ref, pos'.ref, cand'.ref, mode'.ref, k'.ref, v'.ref, tot'.ref, wa'.ref, need'.ref, win'.ref])

set_option maxRecDepth 20000 in
def body : M ctx Wiring := do
  let scan ← rd gBase 4
  let sum ← rd (gBase + 1) W
  let done ← rd (gBase + 2) 1
  let answer ← rd (gBase + 3) W
  let mut nexts : Array Nat := #[]
  let mut ios : Array LaneIO := #[]
  for l in [0:lanes] do
    let (io, ns) ← lane l
    nexts := nexts ++ ns
    ios := ios.push io
  let allDone ← allTree (ios.toList.map (·.done))
  let scanning ← and1 allDone (← ltK scan lanes)
  let sum' ← ite' scanning (← add sum (← pick scan (ios.map (·.tot)))) sum
  let scan' ← ite' scanning (← addK scan 1) scan
  let finished ← and1 allDone (← and1 (← eqK scan lanes) (← not1 done))
  let answer' ← ite' finished sum answer
  let done' ← or1 done finished
  pure (solverWiring ⟨done, answer.ref, nexts ++ #[scan'.ref, sum'.ref, done'.ref, answer'.ref], #[]⟩)

def design : Design := single ctx body

def problem : Problem :=
  { number := 43, title := "Sub-string divisibility",
    idea := "Ten lanes (one per last digit) search the pandigital numbers from the right, a digit per cycle, pruning on each three-digit window (each level keeps the residue its window needs, so a candidate costs a table lookup and a compare); digit registers double as the search stack.",
    answerWidth := W, design, reference, maxCycles := 100000 }

end HDLean.Euler.P043
