import Designs.Euler.Kit

/-!
# BCD arithmetic for the Euler designs

Words of decimal digits, four bits each. Addition resolves the decimal carries
with one binary carry chain: every digit's sum, generate (`≥ 10`) and propagate
(`≥ 9`) are computed in parallel, and the carry into each digit is
`((P + G) ⊕ P ⊕ G)` for the propagate and generate vectors. Doubling is
digit-local.
-/
namespace HDLean.Euler
open HDLean.Rtl HDLean.Rtl.Build

/-- Digit `i` of a BCD word. -/
def dig (x : Sig w) (i : Nat) : M c (Sig 4) := slice x (4 * i) 4

/-- Digits `lo … lo + n − 1` as a BCD word. -/
def digs (x : Sig w) (lo n : Nat) : M c (Sig (4 * n)) := slice x (4 * lo) (4 * n)

/-- Add two `n`-digit BCD numbers: `n + 1` digits. Every digit's sum, generate
(`≥ 10`) and propagate (`≥ 9`) in parallel; the decimal carries in one binary
carry chain. -/
def bcdAdd (n : Nat) (a b : Sig (4 * n)) : M c (Sig (4 * (n + 1))) := do
  let mut sums : List (Sig 5) := []
  let mut gs : List (Sig 1) := []
  let mut ps : List (Sig 1) := []
  for i in [0:n] do
    let s ← add (← zx (← dig a i) 5) (← zx (← dig b i) 5)
    sums := sums ++ [s]
    gs := gs ++ [← geK s 10]
    ps := ps ++ [← geK s 9]
  let pack (bits : List (Sig 1)) : M c (Sig (n + 1)) := do
    let mut acc ← lit (n + 1) 0
    for i in [0:n] do
      acc ← or acc (← shlK (← zx bits[i]! (n + 1)) i)
    pure acc
  let pw ← pack ps
  let gw ← pack gs
  let carries ← xor (← xor (← add pw gw) pw) gw
  let mut out ← shlK (← zx (← bit carries n) (4 * (n + 1))) (4 * n)
  for i in [0:n] do
    let cin ← zx (← bit carries i) 5
    let cout ← bit carries (i + 1)
    let t ← add sums[i]! cin
    let fix ← ite' cout (← lit 5 6) (← lit 5 0)
    let d ← slice (← add t fix) 0 4
    out ← or out (← shlK (← zx d (4 * (n + 1))) (4 * i))
  pure out

/-- Add two `n`-digit BCD numbers and a carry: `n + 1` digits. The carry enters
the binary carry chain as an extra lowest position (generated and propagated by
itself), so there is still one chain. -/
def bcdAddC (n : Nat) (a b : Sig (4 * n)) (cin : Sig 1) : M c (Sig (4 * (n + 1))) := do
  let mut sums : List (Sig 5) := []
  let mut gs : List (Sig 1) := [cin]
  let mut ps : List (Sig 1) := [cin]
  for i in [0:n] do
    let s ← add (← zx (← dig a i) 5) (← zx (← dig b i) 5)
    sums := sums ++ [s]
    gs := gs ++ [← geK s 10]
    ps := ps ++ [← geK s 9]
  let pack (bits : List (Sig 1)) : M c (Sig (n + 2)) := do
    let mut acc ← lit (n + 2) 0
    for i in [0:n + 1] do
      acc ← or acc (← shlK (← zx bits[i]! (n + 2)) i)
    pure acc
  let pw ← pack ps
  let gw ← pack gs
  -- carry into digit i is bit i + 1 of the chain
  let carries ← xor (← xor (← add pw gw) pw) gw
  let mut out ← shlK (← zx (← bit carries (n + 1)) (4 * (n + 1))) (4 * n)
  for i in [0:n] do
    let ci ← zx (← bit carries (i + 1)) 5
    let co ← bit carries (i + 2)
    let t ← add sums[i]! ci
    let fix ← ite' co (← lit 5 6) (← lit 5 0)
    let d ← slice (← add t fix) 0 4
    out ← or out (← shlK (← zx d (4 * (n + 1))) (4 * i))
  pure out

/-- Double an `n`-digit BCD number: `n + 1` digits, without a carry chain. -/
def bcdDouble (n : Nat) (a : Sig (4 * n)) : M c (Sig (4 * (n + 1))) := do
  let mut out ← lit (4 * (n + 1)) 0
  for i in [0:n + 1] do
    let low ← if i < n then rom (← dig a i) 4 fun d => 2 * d % 10 else lit 4 0
    let cin ← if i > 0 then do zx (← geK (← dig a (i - 1)) 5) 4 else lit 4 0
    let d ← or low cin
    out ← or out (← shlK (← zx d (4 * (n + 1))) (4 * i))
  pure out

end HDLean.Euler
