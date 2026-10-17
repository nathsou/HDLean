import Designs.Euler.Bcd

/-!
# Problem 25: 1000-digit Fibonacci number

The index of the first Fibonacci number with 1000 digits.

The leading digits of `F_k` are kept as an 18-digit BCD window (zero padded at
first), two terms per cycle: `(a, b) ↦ (a + b, a + 2b)` (doubling a BCD number
is digit-local, each addition is one carry chain). When `a + 2b` reaches 19
digits both terms drop their last digit and a counter of dropped digits goes up,
so a term has `dropped + 1` digits, or `dropped + 2` when its window has 19. The
truncation error stays below `10^-13` of the value over the run, and no term
near the end lies that close to a power of ten.
-/
namespace HDLean.Euler.P025
open HDLean.Rtl HDLean.Rtl.Build

def digitsWanted : Nat := 1000

def reference (_ : Unit) : Nat := Id.run do
  let mut a := 1
  let mut b := 1
  for k in [3:10000] do
    let c := a + b
    a := b
    b := c
    if c ≥ 10 ^ (digitsWanted - 1) then return k
  return 0

def G : Nat := 18
def W : Nat := 16

def regs : Array RegSpec := #[
  rs "a" (4 * G) (.sync (1 <<< (4 * (G - 1)))),
  rs "b" (4 * G) (.sync (1 <<< (4 * (G - 1)))),
  rs "k" W (.sync 2), rs "drop" 11 (.sync 0), rs "done" 1 (.sync 0), rs "answer" W (.sync 0)]

def ctx : Ctx := solverCtx "euler25" W regs

def body : M ctx Wiring := do
  let a ← rd 0 (4 * G)
  let b ← rd 1 (4 * G)
  let k ← rd 2 W
  let drop ← rd 3 11
  let done ← rd 4 1
  let answer ← rd 5 W
  -- s1 = F(k+1) = a + b, s2 = F(k+2) = a + 2b, with G + 1 digits
  let s1 ← bcdAdd G a b
  let b2 ← bcdDouble G b
  let s2 ← slice (← bcdAdd (G + 1) (← zx a (4 * (G + 1))) b2) 0 (4 * (G + 1))
  let top1 ← neK (← dig s1 G) 0
  let over ← neK (← dig s2 G) 0
  -- digit counts: drop + 1, or drop + 2 with a digit in position G
  let need ← lit 11 (digitsWanted - 2)
  let long1 ← or1 (← ult need drop) (← and1 (← eq drop need) top1)
  let long2 ← or1 (← ult need drop) (← and1 (← eq drop need) over)
  let running ← not1 done
  let found ← and1 running (← or1 long1 long2)
  let answer' ← ite' found (← ite' long1 (← addK k 1) (← addK k 2)) answer
  let done' ← or1 done found
  let a' ← ite' over (← digs s1 1 G) (← digs s1 0 G)
  let b' ← ite' over (← digs s2 1 G) (← digs s2 0 G)
  let drop' ← ite' over (← addK drop 1) drop
  pure (solverWiring ⟨done, answer.ref, #[a'.ref, b'.ref, (← addK k 2).ref, drop'.ref, done'.ref, answer'.ref], #[]⟩)

def design : Design := single ctx body

def problem : Problem :=
  { number := 25, title := "1000-digit Fibonacci number",
    idea := "The leading digits of the Fibonacci numbers as an 18-digit BCD window, two terms per cycle (one carry chain per addition), with a count of the digits dropped; a term's length is that count plus its window's.",
    answerWidth := W, design, reference, maxCycles := 10000 }

end HDLean.Euler.P025
