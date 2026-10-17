import HDLean

/-!
# A small kit for Project Euler designs

Every solver is a single-clock word-level module with one input, `start`
(tied high on the board), and two outputs, `done` and `answer`. It is held in
reset by the board shell, then runs until `done` rises; `answer` is valid from
then on. Registers and memories are declared up front in the module context;
the program reads them, computes, and returns the wiring (outputs, next
register values, memory write ports).

These designs are checked by simulation against plain Lean references and by
external simulators; they carry no proofs yet.
-/
namespace HDLean.Euler
open HDLean.Rtl HDLean.Rtl.Build

instance : Inhabited (Sig w) := ⟨⟨0⟩⟩

def rs (name : String) (w : Nat) (r : Reset := .none) : RegSpec := ⟨Ident.ofString name, w, r⟩
def ms (name : String) (aw w : Nat) (ports : Nat := 1) : MemSpec := ⟨Ident.ofString name, aw, w, ports⟩

/-- The interface of a solver. -/
def solverCtx (name : String) (answer : Nat) (regs : Array RegSpec) (mems : Array MemSpec := #[]) : Ctx :=
  { name := Ident.ofString name, inputs := #[⟨Ident.ofString "start", 1⟩],
    outputs := #[⟨Ident.ofString "done", 1⟩, ⟨Ident.ofString "answer", answer⟩], regs, mems }

/-- What a solver body returns. -/
structure Result where
  done : Sig 1
  answer : Nat
  nexts : Array Nat
  writes : Array (Array WritePort) := #[]

def solverWiring (r : Result) : Wiring := ⟨#[r.done.ref, r.answer], r.nexts, r.writes⟩

/-- A one-module design; empty if the program fails its checks. -/
def single (c : Ctx) (p : M c Wiring) : Design := ⟨#[c.module p]⟩

/-- Why a program fails the builder's checks (for debugging). -/
def diagnose (c : Ctx) (p : M c Wiring) : String :=
  match p (init c) with
  | none => "an operation failed its width or reference check"
  | some (r, s) =>
    s!"outputs {r.outputs.size}/{c.outputs.size}, registers {r.nexts.size}/{c.regs.size}, " ++
    s!"memories {r.writes.size}/{c.mems.size}, ports {(c.mems.zip r.writes).map fun q => (q.2.size, q.1.ports)}, " ++
    s!"ctx ok {c.ok}, module check {(s.toModule r).check c.subs}"

/-- Whether the program passes every builder check. -/
def builds (c : Ctx) (p : M c Wiring) : Bool := (run c p).isSome

section Ops
variable {c : Ctx}

def lit (w v : Nat) : M c (Sig w) := const w (BitVec.ofNat w v)
def rd (k w : Nat) : M c (Sig w) := regRead k w
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
  design : Design
  /-- The answer, computed in plain Lean. -/
  reference : Unit → Nat
  /-- An upper bound on the cycles to `done`, for simulators. -/
  maxCycles : Nat

end HDLean.Euler
