import HDLean.Rtl.Semantics
import HDLean.Rtl.Valid

/-!
# Building word-level modules

`M c` is a builder for one module with interface `c`. It allocates cells and
returns typed handles `Sig w`. Every operation checks widths and references when
it runs and fails closed, so an accepted state is well-formed by construction
(the proofs live in the state).

Registers and memories are declared in the module context `c` (typed state
records produce them). A program reads them like any other cell and *returns*
the wiring: output values, next register values and memory write ports. This
is the Mealy-machine style of the specifications, and it keeps every proof fact
monotone.

Proofs about a builder program use `Ensures` (a Hoare triple) and `Refines`
(a handle denotes a `BitVec`-valued function of the cycle environment). Each
primitive has a lemma, so a design proof composes primitive lemmas instead of
unfolding a concrete netlist.
-/
namespace HDLean.Rtl.Build

/-- A cell of width `w`. -/
structure Sig (w : Nat) where
  ref : Nat
  deriving Repr, DecidableEq

structure RegSpec where
  name : Ident
  width : Nat
  reset : Reset := .none
  deriving Repr, DecidableEq

structure MemSpec where
  name : Ident
  addrWidth : Nat
  width : Nat
  ports : Nat := 1
  deriving Repr, DecidableEq

/-- The interface and state declarations of the module under construction. -/
structure Ctx where
  name : Ident
  inputs : Array Port
  outputs : Array Port
  regs : Array RegSpec := #[]
  mems : Array MemSpec := #[]
  /-- Input and output widths of the modules this module may instantiate. -/
  subs : Array (List Nat × List Nat) := #[]

def Ctx.scope (c : Ctx) : Scope :=
  ⟨c.inputs.map Port.width, c.regs.map RegSpec.width, c.mems.map fun m => (m.addrWidth, m.width), c.subs⟩

def _root_.HDLean.Rtl.Reset.fits (w : Nat) : Reset → Bool
  | .none => true
  | .sync v => decide (v < 2 ^ w)

/-- Every declared width is positive and every reset value fits. -/
def Ctx.ok (c : Ctx) : Bool :=
  c.inputs.toList.all (fun p => 0 < p.width) && c.outputs.toList.all (fun p => 0 < p.width) &&
  c.regs.toList.all (fun r => 0 < r.width && r.reset.fits r.width) &&
  c.mems.toList.all (fun m => 0 < m.addrWidth && 0 < m.width)

structure State (c : Ctx) where
  cells : Array Cell
  widths : Array Nat
  widths_eq : widths = cells.map Cell.width
  valid : cellsValid c.scope cells = true

abbrev M (c : Ctx) := StateT (State c) Option

def init (c : Ctx) : State c := ⟨#[], #[], by simp, rfl⟩

/-- Append a cell after checking its widths and references. -/
def emit (w : Nat) (op : Op) : M c (Sig w) := fun s =>
  if h : (0 < w && op.valid c.scope s.widths w) = true then
    some (⟨s.cells.size⟩,
      { cells := s.cells.push ⟨w, op⟩
        widths := s.widths.push w
        widths_eq := by simp [s.widths_eq]
        valid := by
          rw [cellsValid_push, s.valid]
          simpa [← s.widths_eq] using h })
  else none

/-! ## Typed operations -/

def const (w : Nat) (v : BitVec w) : M c (Sig w) := emit w (.const v.toNat)
def input (k w : Nat) : M c (Sig w) := emit w (.input k)
def regRead (k w : Nat) : M c (Sig w) := emit w (.reg k)
def memRead (k w : Nat) (a : Sig aw) : M c (Sig w) := emit w (.memRead k a.ref)
def not (a : Sig w) : M c (Sig w) := emit w (.not a.ref)
def neg (a : Sig w) : M c (Sig w) := emit w (.neg a.ref)
/-- A non-shift binary operator. -/
def bin (op : BinOp) (a b : Sig w) : M c (Sig w) := emit w (.bin op a.ref b.ref)
/-- A shift by an unsigned amount of any width. -/
def shift (op : BinOp) (a : Sig w) (b : Sig v) : M c (Sig w) := emit w (.bin op a.ref b.ref)
def cmp (op : CmpOp) (a b : Sig w) : M c (Sig 1) := emit 1 (.cmp op w a.ref b.ref)
def mux (s : Sig 1) (a b : Sig w) : M c (Sig w) := emit w (.mux s.ref a.ref b.ref)
def slice (a : Sig v) (lo w : Nat) : M c (Sig w) := emit w (.slice a.ref lo)
def concat (h : Sig v) (l : Sig u) : M c (Sig (v + u)) := emit (v + u) (.concat h.ref l.ref u)
def zext (a : Sig v) (w : Nat) : M c (Sig w) := emit w (.zext a.ref)
def sext (a : Sig v) (w : Nat) : M c (Sig w) := emit w (.sext a.ref v)
/-- An instance of module `j`; the result is its outputs, concatenated. -/
def inst (j : Nat) (args outs : List Nat) : M c (Sig outs.sum) := emit outs.sum (.inst j args outs)

def add (a b : Sig w) : M c (Sig w) := bin .add a b
def sub (a b : Sig w) : M c (Sig w) := bin .sub a b
def mul (a b : Sig w) : M c (Sig w) := bin .mul a b
def udiv (a b : Sig w) : M c (Sig w) := bin .udiv a b
def umod (a b : Sig w) : M c (Sig w) := bin .umod a b
def and (a b : Sig w) : M c (Sig w) := bin .and a b
def or (a b : Sig w) : M c (Sig w) := bin .or a b
def xor (a b : Sig w) : M c (Sig w) := bin .xor a b
def nand (a b : Sig w) : M c (Sig w) := bin .nand a b
def nor (a b : Sig w) : M c (Sig w) := bin .nor a b
def xnor (a b : Sig w) : M c (Sig w) := bin .xnor a b
def shl (a : Sig w) (b : Sig v) : M c (Sig w) := shift .shl a b
def lshr (a : Sig w) (b : Sig v) : M c (Sig w) := shift .lshr a b
def ashr (a : Sig w) (b : Sig v) : M c (Sig w) := shift .ashr a b
def eq (a b : Sig w) : M c (Sig 1) := cmp .eq a b
def ne (a b : Sig w) : M c (Sig 1) := cmp .ne a b
def ult (a b : Sig w) : M c (Sig 1) := cmp .ult a b
def ule (a b : Sig w) : M c (Sig 1) := cmp .ule a b
def slt (a b : Sig w) : M c (Sig 1) := cmp .slt a b
def sle (a b : Sig w) : M c (Sig 1) := cmp .sle a b

/-! ## Finishing a module -/

/-- What a program returns: one cell per output, per register and per write port. -/
structure Wiring where
  outputs : Array Nat
  nexts : Array Nat
  writes : Array (Array WritePort)
  deriving Repr, DecidableEq

def State.toModule (s : State c) (r : Wiring) : Module :=
  ⟨c.name, c.inputs, (c.outputs.zip r.outputs).map (fun p => ⟨p.1.name, p.2⟩), s.cells,
    (c.regs.zip r.nexts).map (fun p => ⟨p.1.name, p.1.width, p.1.reset, p.2⟩),
    (c.mems.zip r.writes).map (fun p => ⟨p.1.name, p.1.addrWidth, p.1.width, p.2⟩)⟩

/-- The returned wiring has one entry for every declared slot. -/
def Wiring.fits (c : Ctx) (r : Wiring) : Bool :=
  r.outputs.size == c.outputs.size && r.nexts.size == c.regs.size && r.writes.size == c.mems.size &&
  (c.mems.zip r.writes).all fun p => p.2.size == p.1.ports

/-- Run a builder program. Fails closed on any malformed allocation or wiring. -/
def run (c : Ctx) (program : M c Wiring) : Option Module := do
  let (r, s) ← program (init c)
  let m := s.toModule r
  if c.ok && r.fits c && m.check c.subs then some m else none

end HDLean.Rtl.Build
