import Designs.Euler.Kit

/-!
# Problem 97: large non-Mersenne prime

The last ten digits of `28433 × 2^7830457 + 1`.

Modulo `10^10 = 2^10 · 5^10`, by the Chinese remainder theorem. Modulo `5^10`
(24-bit residues): left-to-right square-and-multiply, where multiplying by two is
a doubling with one conditional subtraction, so only the 23 squarings and the
final multiplication by 28433 need the modular multiplier: radix 4, interleaved
(`acc ← 4·acc + d·B mod M`, two bits of `A` per cycle, twelve cycles), with the
seven candidate reductions `t − k·M` computed side by side and the largest
non-negative one kept. Modulo `2^10` the same steps run on a ten-bit register
(squaring by a ten-bit multiplier, doubling by a shift). The two residues are
combined at the end: `X = a + 5^10 · ((b − a) · 5^-10 mod 2^10)`, serially.
-/
namespace HDLean.Euler.P097
open HDLean.Rtl HDLean.Rtl.Build

def MOD : Nat := 10 ^ 10
def M5 : Nat := 5 ^ 10
def E : Nat := 7830457
def K : Nat := 28433
/-- Digits of `A` handled per multiplication: 24 bits, radix 4. -/
def digits : Nat := 12
def RW : Nat := 24        -- residues modulo 5^10
def YW : Nat := 28        -- candidate reductions, two's complement
def W : Nat := 34

/-- `5^-10 mod 2^10`. -/
def inv5 : Nat := ((List.range 1024).find? fun t => (t * M5) % 1024 == 1).getD 0

def reference (_ : Unit) : Nat := (K * Nat.pow 2 E + 1) % MOD

-- state encoding
def sSquare := 0   -- load the operands of a squaring
def sPrep := 1     -- reductions for the first digit
def sMul := 2      -- multiplier running
def sAfter := 3    -- multiplication finished
def sDouble := 4
def sFinal := 5    -- load the operands of the multiplication by K
def sFinish := 6   -- multiplication by K finished: combine the residues
def sCrt := 7

/-- The seven candidate reductions per digit. -/
def ks : List Nat := List.range 7

def regs : Array RegSpec := #[
  rs "state" 3 (.sync sSquare), rs "r" RW (.sync 1), rs "a" RW, rs "b" (RW + 1), rs "b3" (RW + 2), rs "acc" RW,
  rs "cnt" 5, rs "idx" 5 (.sync 22), rs "last" 1 (.sync 0), rs "done" 1 (.sync 0), rs "answer" W (.sync 0),
  rs "r2" 10 (.sync 1), rs "tt" 10 (.sync 0), rs "x" W (.sync 0), rs "mb" W (.sync 0)] ++
  (ks.map fun k => rs s!"y{k}" YW).toArray

def ctx : Ctx := solverCtx "euler97" W regs

/-- `d·B − k·M` for each `k`, as two's complement, for the digit `d`. -/
def reductions (d : Sig 2) (b : Sig (RW + 1)) (b3 : Sig (RW + 2)) : M ctx (List (Sig YW)) := do
  let d1 ← bit d 0
  let d2 ← bit d 1
  let bY ← zx b YW
  let b2 ← shlK bY 1
  let b3Y ← zx b3 YW
  let zero ← lit YW 0
  let lo ← ite' d1 bY zero
  let hi ← ite' d1 b3Y b2
  let dB ← ite' d2 hi lo
  ks.mapM fun k => subK dB (k * M5)

def body : M ctx Wiring := do
  let st ← rd 0 3
  let r ← rd 1 RW
  let a ← rd 2 RW
  let b ← rd 3 (RW + 1)
  let b3 ← rd 4 (RW + 2)
  let acc ← rd 5 RW
  let cnt ← rd 6 5
  let idx ← rd 7 5
  let last ← rd 8 1
  let done ← rd 9 1
  let answer ← rd 10 W
  let r2 ← rd 11 10
  let tt ← rd 12 10
  let x ← rd 13 W
  let mb ← rd 14 W
  let ys ← ks.mapM fun k => rd (15 + k) YW
  let isSquare ← eqK st sSquare
  let isPrep ← eqK st sPrep
  let isMul ← eqK st sMul
  let isAfter ← eqK st sAfter
  let isDouble ← eqK st sDouble
  let isFinal ← eqK st sFinal
  let isFinish ← eqK st sFinish
  let isCrt ← eqK st sCrt
  -- one radix-4 step: the candidates 4·acc + d·B − k·M, keep the last non-negative one
  let acc4 ← shlK (← zx acc YW) 2
  let ts ← ys.mapM fun y => add acc4 y
  let mut red ← slice ts[0]! 0 RW
  for k in [1:7] do
    let neg ← bit ts[k]! (YW - 1)
    red ← ite' neg red (← slice ts[k]! 0 RW)
  -- the reductions for the next digit (or the first one, in sPrep)
  let dNext ← ite' isPrep (← slice a (RW - 2) 2) (← slice a (RW - 4) 2)
  let ys' ← reductions dNext b b3
  let cnt0 ← eqK cnt 0
  let a' ← shlK a 2
  let cntDec ← subK cnt 1
  -- doubling: r = 2r mod M
  let r2x ← shlK (← zx r (RW + 1)) 1
  let rge ← geK r2x M5
  let rDbl ← slice (← ite' rge (← subK r2x M5) r2x) 0 RW
  -- exponent bit at idx
  let eBits ← lit 23 E
  let eBit ← bit (← lshr eBits idx) 0
  let idx0 ← eqK idx 0
  let idxDec ← subK idx 1
  -- operands for a new multiplication
  let rB ← zx r (RW + 1)
  let r3 ← add (← zx r (RW + 2)) (← shlK (← zx r (RW + 2)) 1)
  let kLit ← lit RW K
  let zeroR ← lit RW 0
  -- next state
  let afterNext ← ite' last (← lit 3 sFinish) (← ite' eBit (← lit 3 sDouble) (← ite' idx0 (← lit 3 sFinal) (← lit 3 sSquare)))
  let doubleNext ← ite' idx0 (← lit 3 sFinal) (← lit 3 sSquare)
  let mulNext ← ite' cnt0 (← lit 3 sAfter) (← lit 3 sMul)
  let start ← or1 isSquare isFinal
  let st1 ← ite' start (← lit 3 sPrep) st
  let st2 ← ite' isPrep (← lit 3 sMul) st1
  let st3 ← ite' isMul mulNext st2
  let st4 ← ite' isAfter afterNext st3
  let st5 ← ite' isDouble doubleNext st4
  let st' ← ite' isFinish (← lit 3 sCrt) st5
  -- operand registers
  let aNew ← ite' isFinal kLit r
  let a'' ← ite' start aNew (← ite' isMul a' a)
  let b'' ← ite' start rB b
  let b3'' ← ite' start r3 b3
  let acc'' ← ite' start zeroR (← ite' isMul red acc)
  let cnt'' ← ite' start (← lit 5 (digits - 1)) (← ite' isMul cntDec cnt)
  -- r: result of a squaring, or doubled; r2 alongside, modulo 2^10
  let afterSq ← and1 isAfter (← not1 last)
  let r1 ← ite' afterSq acc r
  let r' ← ite' isDouble rDbl r1
  let r2' ← ite' afterSq (← mul r2 r2) (← ite' isDouble (← shlK r2 1) r2)
  -- step the exponent bit after the squaring (and doubling, if any) of this bit
  let leaveBit ← or1 (← and1 afterSq (← not1 eBit)) isDouble
  let idx' ← ite' leaveBit idxDec idx
  let last' ← or1 last isFinal
  -- the residues of K·2^E + 1: a = acc + 1 mod 5^10, b = K·r2 + 1 mod 2^10;
  -- then X = a + 5^10·t with t = (b − a)·5^-10 mod 2^10, over t's bits
  let aRes ← ite' (← eqK acc (M5 - 1)) zeroR (← addK acc 1)
  let bRes ← addK (← mulK r2 K) 1
  let tVal ← mulK (← sub bRes (← resize aRes 10)) inv5
  let tt' ← ite' isFinish tVal (← ite' isCrt (← shrK tt 1) tt)
  let x' ← ite' isFinish (← zx aRes W) (← ite' (← and1 isCrt (← bit tt 0)) (← add x mb) x)
  let mb' ← ite' isFinish (← lit W M5) (← ite' isCrt (← shlK mb 1) mb)
  let finished ← and1 isCrt (← and1 (← eqK tt 0) (← not1 done))
  let answer' ← ite' finished x answer
  let done' ← or1 done finished
  let nexts := #[st'.ref, r'.ref, a''.ref, b''.ref, b3''.ref, acc''.ref, cnt''.ref, idx'.ref, last'.ref,
    done'.ref, answer'.ref, r2'.ref, tt'.ref, x'.ref, mb'.ref] ++ (ys'.map (·.ref)).toArray
  pure (solverWiring ⟨done, answer.ref, nexts, #[]⟩)

def design : Design := single ctx body

def problem : Problem :=
  { number := 97, title := "Large non-Mersenne prime",
    idea := "By the Chinese remainder theorem: square-and-multiply modulo 5^10 with a radix-4 interleaved modular multiplier (doublings are a shift and one conditional subtraction), the same steps modulo 2^10 on a ten-bit register, the residues combined at the end.",
    answerWidth := W, design, reference, maxCycles := 2000 }

end HDLean.Euler.P097
