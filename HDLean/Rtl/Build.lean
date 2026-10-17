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

/-- Why a builder program was rejected. -/
structure BuildError where
  /-- What failed, with the widths involved. -/
  msg : String
  /-- The enclosing `scope` labels, outermost first. -/
  trail : List String := []
  /-- The number of cells allocated before the failure. -/
  cells : Nat := 0
  deriving Repr, Inhabited

def BuildError.render (e : BuildError) : String :=
  let path := if e.trail.isEmpty then "" else " > ".intercalate e.trail ++ ": "
  s!"{path}{e.msg} (after {e.cells} cells)"

instance : ToString BuildError := ⟨BuildError.render⟩

abbrev M (c : Ctx) := StateT (State c) (Except BuildError)

def init (c : Ctx) : State c := ⟨#[], #[], by simp, rfl⟩

private def showW : Option Nat → String
  | some w => toString w
  | none => "missing"

/-- "a 16-bit" or "an 8-bit" value. -/
private def aBits : Option Nat → String
  | some w =>
    let t := toString w
    if t.startsWith "8" || w == 11 || w == 18 then s!"an {t}-bit" else s!"a {t}-bit"
  | none => "a missing"

def _root_.HDLean.Rtl.BinOp.name : BinOp → String
  | .and => "and" | .or => "or" | .xor => "xor" | .nand => "nand" | .nor => "nor" | .xnor => "xnor"
  | .add => "add" | .sub => "sub" | .mul => "mul" | .udiv => "udiv" | .umod => "umod"
  | .shl => "shl" | .lshr => "lshr" | .ashr => "ashr"

def _root_.HDLean.Rtl.CmpOp.name : CmpOp → String
  | .eq => "eq" | .ne => "ne" | .ult => "ult" | .ule => "ule" | .slt => "slt" | .sle => "sle"

/-- Why a cell of width `w` is rejected: the first failing condition of
`0 < w && op.valid`, in words. -/
def _root_.HDLean.Rtl.Op.explain (sc : Scope) (ws : Array Nat) (w : Nat) (op : Op) : String :=
  let wd (k : Nat) := showW ws[k]?
  if w = 0 then s!"zero-width result ({repr op})" else
  match op with
  | .const v => s!"constant {v} does not fit in {w} bits"
  | .input k => s!"input {k} is {showW sc.inputs[k]?} bits, read as {w}"
  | .reg k => s!"register {k} is {showW sc.regs[k]?} bits, read as {w}"
  | .memRead mi a => match sc.mems[mi]? with
    | some (aw, mw) => s!"memory {mi} ({aw}-bit address, {mw}-bit words): read as {w} bits at {aBits ws[a]?} address"
    | none => s!"memory {mi} is not declared"
  | .not a => s!"not: operand is {wd a} bits, result {w}"
  | .neg a => s!"neg: operand is {wd a} bits, result {w}"
  | .bin op a b => s!"{op.name}: operands are {wd a} and {wd b} bits, result {w}"
  | .cmp op cw a b => s!"{op.name}: operands are {wd a} and {wd b} bits, compared at {cw}"
  | .mux sel a b => s!"mux: select is {wd sel} bits, arms are {wd a} and {wd b}, result {w}"
  | .slice a lo => s!"slice: bits {lo} … {lo + w - 1} of {aBits ws[a]?} value"
  | .concat h l lw => s!"concat: {wd h} and {wd l} bits (low part declared {lw}), result {w}"
  | .zext a => s!"zero extension from {wd a} to {w} bits (narrower: use a slice)"
  | .sext a fw => s!"sign extension of {aBits ws[a]?} value (declared {fw}) to {w} bits"
  | .inst j args outs => match sc.subs[j]? with
    | some (ins, outs') => s!"instance of module {j}: arguments {args.map (showW ws[·]?)} for inputs {ins}, outputs {outs} for {outs'}, result {w}"
    | none => s!"module {j} cannot be instantiated here"

/-- Append a cell after checking its widths and references. -/
def emit (w : Nat) (op : Op) : M c (Sig w) := fun s =>
  if h : (0 < w && op.valid c.scope s.widths w) = true then
    .ok (⟨s.cells.size⟩,
      { cells := s.cells.push ⟨w, op⟩
        widths := s.widths.push w
        widths_eq := by simp [s.widths_eq]
        valid := by
          rw [cellsValid_push, s.valid]
          simpa [← s.widths_eq] using h })
  else .error { msg := op.explain c.scope s.widths w, cells := s.cells.size }

/-- Reject the program with a message. -/
def fail (msg : String) : M c α := fun s => .error { msg, cells := s.cells.size }

/-- Run `m`, naming it in the trail of any error it raises. -/
def scope (name : String) (m : M c α) : M c α := fun s =>
  match m s with
  | .error e => .error { e with trail := name :: e.trail }
  | .ok r => .ok r

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

/-- Why a context is malformed. -/
def Ctx.explain (c : Ctx) : String :=
  let bad := (c.inputs.toList.filter (fun p => p.width == 0)).map (fun p => s!"input {p.name}") ++
    (c.outputs.toList.filter (fun p => p.width == 0)).map (fun p => s!"output {p.name}") ++
    (c.regs.toList.filter (fun r => !(0 < r.width && r.reset.fits r.width))).map (fun r =>
      s!"register {r.name} ({r.width} bits, reset {repr r.reset})") ++
    (c.mems.toList.filter (fun m => !(0 < m.addrWidth && 0 < m.width))).map (fun m => s!"memory {m.name}")
  s!"malformed declarations: {", ".intercalate bad}"

/-- Why a wiring does not fit its context, or why the module fails its check. -/
def Wiring.explain (c : Ctx) (s : State c) (r : Wiring) : String :=
  let width (k : Nat) := s.widths[k]?
  if r.outputs.size != c.outputs.size then
    s!"{r.outputs.size} outputs wired, {c.outputs.size} declared"
  else if r.nexts.size != c.regs.size then
    s!"{r.nexts.size} next values for {c.regs.size} registers"
  else if r.writes.size != c.mems.size then
    s!"write ports for {r.writes.size} memories, {c.mems.size} declared ({", ".intercalate (c.mems.toList.map (·.name.text))})"
  else
    let regs := (c.regs.zip r.nexts).toList.filterMap fun (g, n) =>
      if width n == some g.width then none else some s!"register {g.name} ({g.width} bits) gets {aBits (width n)} value"
    let mems := (c.mems.zip r.writes).toList.filterMap fun (m, ps) =>
      if ps.size != m.ports then some s!"memory {m.name}: {ps.size} write ports, {m.ports} declared"
      else if ps.all (fun p => width p.en == some 1 && width p.addr == some m.addrWidth && width p.data == some m.width) then none
      else some s!"memory {m.name}: write port widths {ps.toList.map fun p => (showW (width p.en), showW (width p.addr), showW (width p.data))}, expected (1, {m.addrWidth}, {m.width})"
    let outs := (c.outputs.zip r.outputs).toList.filterMap fun (o, n) =>
      if (width n).isSome then none else some s!"output {o.name} is wired to a missing cell"
    match regs ++ mems ++ outs with
    | [] => "the finished module fails its check"
    | es => "; ".intercalate es

/-- Outputs wired to cells of other widths than their ports (not caught by `Module.check`). -/
def Wiring.badOutputs (c : Ctx) (s : State c) (r : Wiring) : List String :=
  (c.outputs.zip r.outputs).toList.filterMap fun (o, n) =>
    if s.widths[n]? == some o.width then none
    else some s!"output {o.name} ({o.width} bits) is wired to {aBits s.widths[n]?} value"

/-- Run a builder program, explaining any rejection. Besides `run`'s checks, the
outputs must have the widths of their ports. -/
def runE (c : Ctx) (program : M c Wiring) : Except BuildError Module :=
  match program (init c) with
  | .error e => .error e
  | .ok (r, s) =>
    let m := s.toModule r
    if !c.ok then .error { msg := c.explain, cells := s.cells.size }
    else if !(r.fits c && m.check c.subs) then .error { msg := r.explain c s, cells := s.cells.size }
    else match r.badOutputs c s with
      | [] => .ok m
      | es => .error { msg := "; ".intercalate es, cells := s.cells.size }

/-- Run a builder program. Fails closed on any malformed allocation or wiring. -/
def run (c : Ctx) (program : M c Wiring) : Option Module :=
  match program (init c) with
  | .ok (r, s) =>
    let m := s.toModule r
    if c.ok && r.fits c && m.check c.subs then some m else none
  | .error _ => none

theorem run_of_runE {c : Ctx} {program : M c Wiring} {m : Module} (h : runE c program = .ok m) :
    run c program = some m := by
  unfold runE at h
  unfold run
  split at h
  · cases h
  · rename_i r s hp
    rw [hp]
    by_cases hc : c.ok <;> by_cases hf : (r.fits c && (s.toModule r).check c.subs) <;> simp [hc, hf] at h ⊢
    split at h <;> simp_all

end HDLean.Rtl.Build
