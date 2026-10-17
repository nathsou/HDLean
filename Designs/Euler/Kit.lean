import HDLean

/-!
# A small kit for Project Euler designs

Every solver is a single-clock word-level module with one input, `start`
(tied high on the board), and two outputs, `done` and `answer`. It is held in
reset by the board shell, then runs until `done` rises; `answer` is valid from
then on. Its registers are a record (`hdl_record`, composed with `Both` and
`Lanes`), declared with their reset values; the program reads them as handles and
returns `done`, `answer`, the next registers (`{ r with … }`, everything else
holds) and the memory writes. A rejected program is reported with the reason
and the enclosing `scope`s.

These designs are checked by simulation against plain Lean references and by
external simulators; they carry no proofs yet.
-/
namespace HDLean.Euler
open HDLean.Rtl HDLean.Rtl.Build

def ms (name : String) (aw w : Nat) (ports : Nat := 1) : MemSpec := ⟨Ident.ofString name, aw, w, ports⟩

/-- A single word, for `Lanes` of words. -/
hdl_record Word (w : Nat) where
  v : w

hdl_record SolverIn where
  start : 1

hdl_record SolverOut (w : Nat) where
  done : 1
  answer : w

/-- The interface of a solver whose answer is `answer` bits wide and whose
registers are the record `R`, with resets `resets`. -/
def solverCtx (name : String) (answer : Nat) (R : (Nat → Type) → Type) [Bundle R]
    (resets : R (fun _ => Reset)) (mems : Array MemSpec := #[]) : Ctx :=
  Ctx.mealy name SolverIn (SolverOut answer) R resets mems

/-- A solver program: from the registers to `done`, `answer`, the next registers
and the memory writes. The body runs inside `scope name`, so a rejected cell
names the solver. -/
def solver {c : Ctx} {w : Nat} (name : String) (R : (Nat → Type) → Type) [Bundle R]
    (body : R Sig → M c (Step (SolverOut w) R)) : M c Wiring :=
  scope name (mealy SolverIn (SolverOut w) R fun _ r => body r)

/-- The end of a solver cycle. -/
def finish {c : Ctx} {w : Nat} {R : (Nat → Type) → Type} (done : Sig 1) (answer : Sig w) (next : R Sig)
    (writes : Array (Array WritePort) := #[]) : M c (Step (SolverOut w) R) :=
  pure ⟨⟨done, answer⟩, next, writes⟩

/-- The one-module design of a solver, or why the builder rejected it. -/
def solverDesign (c : Ctx) (p : M c Wiring) : Except String Design :=
  match runE c p with
  | .ok m => .ok ⟨#[m]⟩
  | .error e => .error e.render

section Ops
variable {c : Ctx}

def lit (w v : Nat) : M c (Sig w) := const w (BitVec.ofNat w v)
def addK (a : Sig w) (v : Nat) : M c (Sig w) := do add a (← lit w v)
def subK (a : Sig w) (v : Nat) : M c (Sig w) := do sub a (← lit w v)
def eqK (a : Sig w) (v : Nat) : M c (Sig 1) := do eq a (← lit w v)
def neK (a : Sig w) (v : Nat) : M c (Sig 1) := do ne a (← lit w v)
def ltK (a : Sig w) (v : Nat) : M c (Sig 1) := do ult a (← lit w v)
def geK (a : Sig w) (v : Nat) : M c (Sig 1) := do not (← ltK a v)
def and1 (a b : Sig 1) : M c (Sig 1) := and a b
def or1 (a b : Sig 1) : M c (Sig 1) := or a b
def not1 (a : Sig 1) : M c (Sig 1) := not a
/-- `if s then a else b`. -/
def ite' (s : Sig 1) (a b : Sig w) : M c (Sig w) := mux s a b
def bit (a : Sig w) (i : Nat) : M c (Sig 1) := slice a i 1
def zx (a : Sig v) (w : Nat) : M c (Sig w) := zext a w
/-- Shift left by a constant. -/
def shlK (a : Sig w) (k : Nat) : M c (Sig w) := do shl a (← lit w k)
/-- Shift right by a constant. -/
def shrK (a : Sig w) (k : Nat) : M c (Sig w) := do lshr a (← lit w k)
/-- Resize: truncate or zero-extend. -/
def resize (a : Sig v) (w : Nat) : M c (Sig w) :=
  if w ≤ v then slice a 0 w else zext a w

/-- Multiplication by a constant, as a sum of shifted copies (no multiplier). -/
def mulK (a : Sig w) (k : Nat) : M c (Sig w) := do
  let terms ← ((List.range w).filter fun i => (k >>> i) % 2 == 1).mapM fun i => shlK a i
  match terms with
  | [] => lit w 0
  | t :: rest => rest.foldlM (fun acc x => add acc x) t

/-- Sum of a list of words, as a balanced tree. -/
partial def sumTree (xs : List (Sig w)) : M c (Sig w) := do
  match xs with
  | [] => lit w 0
  | [x] => pure x
  | _ =>
    let half := xs.length / 2
    let a ← sumTree (xs.take half)
    let b ← sumTree (xs.drop half)
    add a b

/-- OR of a list of bits. -/
partial def anyTree (xs : List (Sig 1)) : M c (Sig 1) := do
  match xs with
  | [] => lit 1 0
  | [x] => pure x
  | _ => or (← anyTree (xs.take (xs.length / 2))) (← anyTree (xs.drop (xs.length / 2)))

/-- AND of a list of bits. -/
partial def allTree (xs : List (Sig 1)) : M c (Sig 1) := do
  match xs with
  | [] => lit 1 1
  | [x] => pure x
  | _ => and (← allTree (xs.take (xs.length / 2))) (← allTree (xs.drop (xs.length / 2)))

/-- Number of set bits of `a`, at width `w`. -/
def popcount (a : Sig v) (w : Nat) : M c (Sig w) := do
  let bits ← (List.range v).mapM fun i => bit a i
  resize (← countBits bits) w
where
  /-- The count of a list of bits, each adder only as wide as its subtree needs. -/
  countBits (bits : List (Sig 1)) : M c (Sig 8) := do
    let rec go (xs : List (Sig 1)) (fuel : Nat) : M c (Sig 8) := do
      match fuel, xs with
      | 0, _ => lit 8 0
      | _, [] => lit 8 0
      | _, [x] => zx x 8
      | f + 1, _ =>
        let half := xs.length / 2
        let width := Nat.log2 xs.length + 1
        let a ← resize (← go (xs.take half) f) width
        let b ← resize (← go (xs.drop half) f) width
        zx (← add a b) 8
    go bits bits.length

/-- `f base`, …, as a multiplexer tree over the low `b` bits of `idx`. -/
def romAux (idx : Sig iw) (w : Nat) (f : Nat → Nat) : Nat → Nat → M c (Sig w)
  | 0, base => lit w (f base % 2 ^ w)
  | b + 1, base =>
    if (List.range (2 ^ (b + 1))).all fun i => f (base + i) % 2 ^ w == f base % 2 ^ w then lit w (f base % 2 ^ w)
    else do
      let hi ← romAux idx w f b (base + 2 ^ b)
      let lo ← romAux idx w f b base
      ite' (← bit idx b) hi lo

/-- The bit length of `x` (the position of its highest set bit, plus one), as a
balanced tree: `lo` is the position of `x`'s bit 0. -/
partial def bitLenAux (x : Sig w) (lo : Nat) (rw : Nat) : M c (Sig rw) := do
  if w ≤ 1 then
    ite' (← bit x 0) (← lit rw (lo + 1)) (← lit rw 0)
  else
    let half := w / 2
    let low ← slice x 0 half
    let high ← slice x half (w - half)
    let hl ← bitLenAux high (lo + half) rw
    let ll ← bitLenAux low lo rw
    ite' (← ne high (← lit (w - half) 0)) hl ll

/-- The bit length of `x`, at width `rw`. -/
def bitLen (x : Sig w) (rw : Nat) : M c (Sig rw) := bitLenAux x 0 rw

/-- `xs[idx]` (the last element beyond the end), as a tree of multiplexers over the low `b` bits. -/
def pickAux (idx : Sig iw) (xs : Array (Sig w)) : Nat → Nat → M c (Sig w)
  | 0, base => pure (xs[base]?.getD (xs.back?.getD ⟨0⟩))
  | b + 1, base =>
    if base + 2 ^ b ≥ xs.size then pickAux idx xs b base
    else do
      let hi ← pickAux idx xs b (base + 2 ^ b)
      let lo ← pickAux idx xs b base
      ite' (← bit idx b) hi lo

/-- `xs[idx]`, as a tree of multiplexers. -/
def pick (idx : Sig iw) (xs : Array (Sig w)) : M c (Sig w) := pickAux idx xs iw 0

/-- A read-only table: `f idx` (modulo `2 ^ w`), as a tree of multiplexers. -/
def rom (idx : Sig iw) (w : Nat) (f : Nat → Nat) : M c (Sig w) := romAux idx w f iw 0

end Ops

/-! ## Running a solver in Lean -/

/-- Reset for one cycle, then step until `done`; the number of clock edges
after reset release before `done` is seen, and the answer. -/
def simulate (d : Design) (maxCycles : Nat) : Option (Nat × Nat) := Id.run do
  let mut st : Store := d.step default (#[1], true)
  for t in [:maxCycles] do
    let o := d.output st #[1]
    if o.getD 0 0 % 2 == 1 then return some (t, o.getD 1 0)
    st := d.step st (#[1], false)
  return none

/-- A Project Euler problem with its solver. -/
structure Problem where
  number : Nat
  title : String
  /-- What the design does, in a sentence or two. -/
  idea : String
  answerWidth : Nat
  /-- The solver, or why the builder rejected it. -/
  design : Except String Design
  /-- The answer, computed in plain Lean. -/
  reference : Unit → Nat
  /-- An upper bound on the cycles to `done`, for simulators. -/
  maxCycles : Nat

end HDLean.Euler
