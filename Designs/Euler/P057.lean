import Designs.Euler.Bcd

/-!
# Problem 57: square root convergents

In the first thousand expansions `p/q` of the continued fraction of `√2`
(`3/2, 7/5, 17/12, …`, `p' = p + 2q`, `q' = p + q`), how many numerators have
more digits than their denominators?

Exact arithmetic on numbers of up to 384 digits: `p` and `q` live in two block
RAM arrays of 32-digit BCD words (128 bits wide, one word per address). Each
expansion streams the words from the bottom, one per cycle, through a pipeline:
the block RAMs' output registers, a second register, `q' = p + q` (one BCD
addition with carry-in, a single carry chain), `p' = q' + q` (written back in
place with `q'`), and the digit counts from the highest nonzero words (position
of the top nonzero digit). The expansions follow each other without draining
the pipeline: the next one starts reading as soon as the current one has issued
its last word, at least four words each so that every word is written back
before it is read again, one word past the highest top seen so far, for the
carries. An expansion's digit counts are compared when the next one's first
word reaches the last stage.
-/
namespace HDLean.Euler.P057
open HDLean.Rtl HDLean.Rtl.Build

def expansions : Nat := 1000

def reference (_ : Unit) : Nat := Id.run do
  let mut p := 3
  let mut q := 2
  let mut count := 0
  for _ in [:expansions] do
    if (Nat.toDigits 10 p).length > (Nat.toDigits 10 q).length then count := count + 1
    let p' := p + 2 * q
    q := p + q
    p := p'
  return count

def D : Nat := 32             -- digits per word
def BW : Nat := 4 * D
def AW : Nat := 4             -- 16 words: up to 512 digits
def W : Nat := 10
def LW : Nat := 10            -- digit counts

-- phases
def phClear := 0
def phRun := 1
def phDrain := 2
def phDone := 3

hdl_record Regs where
  ph : 2 := phClear
  it : 10 := 1
  w : 5 := 0
  wl : 5 := 3
  top : 5 := 0
  -- stage R (the block RAMs' output registers), S (registered again), A (q' = p + q),
  -- B (p' = q' + q, written back), C (lengths)
  vr : 1 := 0
  wr : AW
  pr : BW
  qr : BW
  vs : 1 := 0
  ws : AW
  ps : BW
  qs : BW
  va : 1 := 0
  wa : AW
  qa : BW
  qqa : BW
  cq : 1 := 0
  cp : 1 := 0
  vc : 1 := 0
  wc : AW
  pc : BW
  qc : BW
  -- digit counts of the expansion going through stage C (initially 3/2)
  plen : LW := 1
  qlen : LW := 1
  count : W := 0
  done : 1 := 0
  answer : W := 0

def mems : Array MemSpec := #[ms "p" AW BW, ms "q" AW BW]

def ctx : Ctx := solverCtx "euler57" W Regs Regs.resets mems

/-- The number of digits of a word: the position of its top nonzero digit, plus one. -/
def wordLen (x : Sig BW) : M ctx (Sig 6) := do
  let nz ← (List.range D).mapM fun i => do neK (← slice x (4 * i) 4) 0
  let mut v ← lit D 0
  for i in [0:D] do
    v ← or v (← shlK (← zx nz[i]! D) i)
  bitLen v 6

set_option maxRecDepth 20000 in
def body : M ctx Wiring := solver "P057" Regs fun g => do
  let ph := g.ph
  let it := g.it
  let w := g.w
  let wl := g.wl
  let top := g.top
  let ws := g.ws
  let ps := g.ps
  let qs := g.qs
  let vs := g.vs
  let va := g.va
  let wa := g.wa
  let qa := g.qa
  let qqa := g.qqa
  let cq := g.cq
  let cp := g.cp
  let vc := g.vc
  let wc := g.wc
  let pc := g.pc
  let qc := g.qc
  let vr := g.vr
  let plen := g.plen
  let qlen := g.qlen
  let count := g.count
  let done := g.done
  let answer := g.answer
  let isClear ← eqK ph phClear
  let isRun ← eqK ph phRun
  let isDrain ← eqK ph phDrain
  let wA ← slice w 0 AW
  -- running: the word at address w (stage R: the block RAMs' outputs)
  let pw ← readMem "p" BW wA
  let qw ← readMem "q" BW wA
  -- stage A: q' = p + q + carry (none into word 0)
  let sA ← bcdAddC D ps qs (← and1 cq (← neK ws 0))
  let qNew ← slice sA 0 BW
  let cq' ← ite' vs (← neK (← slice sA BW 4) 0) cq
  -- stage B: p' = q' + q + carry, written back in place with q'
  let sB ← bcdAddC D qa qqa (← and1 cp (← neK wa 0))
  let pNew ← slice sB 0 BW
  let cp' ← ite' va (← neK (← slice sB BW 4) 0) cp
  -- stage C: the digit counts from the highest nonzero words; word 0 starts a new
  -- expansion, so the previous one is counted then
  let base ← shlK (← zx wc LW) 5
  let pNZ ← neK pc 0
  let qNZ ← neK qc 0
  let first ← and1 vc (← eqK wc 0)
  let zeroL ← lit LW 0
  let plen' ← ite' (← and1 vc pNZ) (← add base (← zx (← wordLen pc) LW)) (← ite' first zeroL plen)
  let qlen' ← ite' (← and1 vc qNZ) (← add base (← zx (← wordLen qc) LW)) (← ite' first zeroL qlen)
  let longer ← ult qlen plen
  let top' ← ite' (← and1 (← and1 vc pNZ) (← ult top (← zx wc 5))) (← zx wc 5) top
  -- writes: clearing (p = 3, q = 2), or stage B
  let w0 ← eqK w 0
  let zero ← lit BW 0
  let clearLast ← eqK w (2 ^ AW - 1)
  let pWrite := port (← or1 isClear va) (← ite' isClear wA wa) (← ite' isClear (← ite' w0 (← lit BW 3) zero) pNew)
  let qWrite := port (← or1 isClear va) (← ite' isClear wA wa) (← ite' isClear (← ite' w0 (← lit BW 2) zero) qa)
  -- control: the expansions follow each other without a gap. Expansion i + 1
  -- reads words 0 … wl; the words of expansion i are written back four cycles
  -- after they are read, so at least four words are read (wl ≥ 3), and the top
  -- word can grow by one per expansion: wl = top + 2, with top the highest word
  -- seen at stage C (it lags, but has seen all of expansion i − 1).
  let lastWord ← and1 isRun (← eq w wl)
  let lastIt ← eqK it (expansions - 1)
  let w' ← ite' isClear (← ite' clearLast (← lit 5 0) (← addK w 1))
    (← ite' isRun (← ite' lastWord (← lit 5 0) (← addK w 1)) w)
  let wl' ← ite' lastWord (← ite' (← eqK top 0) (← lit 5 3) (← addK top 2)) wl
  let it' ← ite' lastWord (← addK it 1) it
  let drained ← and1 isDrain (← not1 (← or1 (← or1 vr vs) (← or1 va vc)))
  let ph' ← ite' (← and1 isClear clearLast) (← lit 2 phRun)
    (← ite' (← and1 lastWord lastIt) (← lit 2 phDrain)
    (← ite' drained (← lit 2 phDone) ph))
  let count' ← ite' (← and1 first longer) (← addK count 1) count
  let finished ← and1 drained (← not1 done)
  let answer' ← ite' finished (← ite' longer (← addK count 1) count) answer
  let done' ← or1 done finished
  finish done answer
    { ph := ph', it := it', w := w', wl := wl', top := top',
      vr := isRun, wr := wA, pr := pw, qr := qw,
      vs := vr, ws := g.wr, ps := g.pr, qs := g.qr,
      cq := cq', cp := cp',
      va := vs, wa := ws, qa := qNew, qqa := qs,
      vc := va, wc := wa, pc := pNew, qc := qa,
      plen := plen', qlen := qlen', count := count', done := done', answer := answer' }
    (← writePorts [("p", #[pWrite]), ("q", #[qWrite])])

def design : Except String Design := solverDesign ctx body

def problem : Problem :=
  { number := 57, title := "Square root convergents",
    idea := "Exact 384-digit BCD numerators and denominators in block RAM, streamed a 32-digit word per cycle through a pipeline (q' = p + q, p' = q' + q written back in place, then the digit lengths from the highest nonzero word), expansions back to back.",
    answerWidth := W, design, reference, maxCycles := 100000 }

end HDLean.Euler.P057
