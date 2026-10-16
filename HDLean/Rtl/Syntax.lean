/-
Word-level RTL: the scalable source language of HDLean.

A design is an ordered list of modules. A module is a finite graph of *cells*,
each producing one bit-vector of a declared width, plus typed registers,
memories and output ports. A cell refers only to earlier cells, so every
module is acyclic by construction. A module may instantiate any *earlier*
module of the design, so the hierarchy is acyclic too.

Everything here is plain data; the meaning is in `Rtl/Semantics.lean`, and
`Module.check`/`Design.check` decide well-formedness (widths and references).
-/
namespace HDLean.Rtl

/-- Characters allowed in user-chosen names. Emitted identifiers are always
prefixed and indexed (`r_3_pc`), so a name can never collide with a keyword or
with another declaration. -/
def identChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- A name that is safe to place inside an emitted identifier. -/
structure Ident where
  text : String
  valid : text.toList.all identChar = true

instance : DecidableEq Ident := fun a b =>
  if h : a.text = b.text then isTrue (by cases a; cases b; simp at h; subst h; rfl)
  else isFalse (by intro e; exact h (congrArg Ident.text e))

instance : Repr Ident := ⟨fun i _ => repr i.text⟩
instance : ToString Ident := ⟨Ident.text⟩

private def fixChar (c : Char) : Char := if identChar c then c else '_'

/-- Total: unsupported characters become `_`. -/
def Ident.ofString (s : String) : Ident :=
  ⟨String.ofList (s.toList.map fixChar), by
    simp only [String.toList_ofList, List.all_map]
    apply List.all_eq_true.mpr
    intro c _
    simp only [Function.comp_apply, fixChar]
    split
    · assumption
    · decide⟩

instance : Coe String Ident := ⟨Ident.ofString⟩
instance : Inhabited Ident := ⟨Ident.ofString ""⟩

/-- Binary word operators. Both operands have the result width, except the
shift amount, which may have any width and is read as an unsigned number. -/
inductive BinOp where
  | and | or | xor | nand | nor | xnor
  | add | sub | mul | udiv | umod
  | shl | lshr | ashr
  deriving Repr, DecidableEq, Inhabited

def BinOp.isShift : BinOp → Bool
  | .shl | .lshr | .ashr => true
  | _ => false

/-- Comparisons produce one bit. -/
inductive CmpOp where
  | eq | ne | ult | ule | slt | sle
  deriving Repr, DecidableEq, Inhabited

/-- A cell operation. Arguments are indices of earlier cells. -/
inductive Op where
  | const (value : Nat)
  | input (port : Nat)
  | reg (index : Nat)
  /-- Combinational read of memory `mem` at the address computed by cell `addr`.
  A registered (block-RAM) read is this cell followed by a register. -/
  | memRead (mem addr : Nat)
  | not (a : Nat)
  | neg (a : Nat)
  | bin (op : BinOp) (a b : Nat)
  /-- Compare `a` and `b`, both `width` bits wide. -/
  | cmp (op : CmpOp) (width a b : Nat)
  /-- `sel` is one bit wide. -/
  | mux (sel a b : Nat)
  /-- Bits `lo .. lo + width - 1` of `a`. -/
  | slice (a lo : Nat)
  /-- `hi` occupies the most significant bits; `lo` is `loWidth` bits wide. -/
  | concat (hi lo loWidth : Nat)
  | zext (a : Nat)
  /-- Sign-extend `a`, which is `fromWidth` bits wide. -/
  | sext (a fromWidth : Nat)
  /-- An instance of an earlier module whose outputs have widths `outs`. The
  cell's value is the concatenation of the instance's outputs, first output in
  the least significant bits. -/
  | inst (module : Nat) (args : List Nat) (outs : List Nat)
  deriving Repr, DecidableEq, Inhabited

structure Cell where
  width : Nat
  op : Op
  deriving Repr, DecidableEq, Inhabited

structure Port where
  name : Ident
  width : Nat
  deriving Repr, DecidableEq, Inhabited

structure OutPort where
  name : Ident
  node : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Registers are either free-running (arbitrary power-up value, no reset) or
synchronously reset to a constant. -/
inductive Reset where
  | none
  | sync (value : Nat)
  deriving Repr, DecidableEq, Inhabited

structure Reg where
  name : Ident
  width : Nat
  reset : Reset
  next : Nat
  deriving Repr, DecidableEq, Inhabited

/-- One synchronous write port. Later ports win on equal addresses. -/
structure WritePort where
  en : Nat
  addr : Nat
  data : Nat
  deriving Repr, DecidableEq, Inhabited

/-- `2 ^ addrWidth` words of `width` bits. Contents are never reset. -/
structure Mem where
  name : Ident
  addrWidth : Nat
  width : Nat
  writes : Array WritePort
  deriving Repr, DecidableEq, Inhabited

structure Module where
  name : Ident
  inputs : Array Port
  outputs : Array OutPort
  cells : Array Cell
  regs : Array Reg
  mems : Array Mem
  deriving Repr, DecidableEq, Inhabited

/-- Modules in dependency order; the last one is the top. -/
structure Design where
  modules : Array Module
  deriving Repr, DecidableEq, Inhabited

namespace Module

def cellWidth (m : Module) (k : Nat) : Nat := (m.cells[k]?.map Cell.width).getD 0

def outWidths (m : Module) : List Nat := m.outputs.toList.map fun o => m.cellWidth o.node

def inWidths (m : Module) : List Nat := m.inputs.toList.map Port.width

/-- Number of instance cells; each owns one slot of the store. -/
def instCount (m : Module) : Nat :=
  m.cells.toList.countP fun c => match c.op with | .inst .. => true | _ => false

end Module

/-! ## Well-formedness -/

/-- What a cell may refer to besides earlier cells. -/
structure Scope where
  inputs : Array Nat
  regs : Array Nat
  mems : Array (Nat × Nat)
  /-- Input and output widths of the modules this one may instantiate. -/
  subs : Array (List Nat × List Nat)

def Op.valid (sc : Scope) (widths : Array Nat) (w : Nat) : Op → Bool
  | .const v => v < 2 ^ w
  | .input k => sc.inputs[k]? == some w
  | .reg k => sc.regs[k]? == some w
  | .memRead mi a => match sc.mems[mi]? with
    | some (aw, mw) => mw == w && widths[a]? == some aw
    | none => false
  | .not a | .neg a => widths[a]? == some w
  | .bin op a b => widths[a]? == some w && (if op.isShift then widths[b]?.isSome else widths[b]? == some w)
  | .cmp _ cw a b => w == 1 && widths[a]? == some cw && widths[b]? == some cw
  | .mux s a b => widths[s]? == some 1 && widths[a]? == some w && widths[b]? == some w
  | .slice a lo => match widths[a]? with
    | some wa => lo + w ≤ wa
    | none => false
  | .concat h l lw => match widths[h]? with
    | some x => widths[l]? == some lw && x + lw == w
    | none => false
  | .zext a => match widths[a]? with
    | some wa => wa ≤ w
    | none => false
  | .sext a fw => widths[a]? == some fw && fw ≤ w
  | .inst j args outs => match sc.subs[j]? with
    | some (ins, outs') => args.map (widths[·]?) == ins.map some && outs == outs' && outs.sum == w
    | none => false

def cellsValidFrom (sc : Scope) : Array Nat → List Cell → Bool
  | _, [] => true
  | ws, c :: cs => 0 < c.width && c.op.valid sc ws c.width && cellsValidFrom sc (ws.push c.width) cs

/-- Every cell is at least one bit wide and refers only to earlier cells. -/
def cellsValid (sc : Scope) (cells : Array Cell) : Bool := cellsValidFrom sc #[] cells.toList

def Module.scope (m : Module) (subs : Array (List Nat × List Nat)) : Scope :=
  ⟨m.inputs.map Port.width, m.regs.map Reg.width, m.mems.map (fun mm => (mm.addrWidth, mm.width)), subs⟩

def Module.check (m : Module) (subs : Array (List Nat × List Nat)) : Bool :=
  let width k := m.cells[k]?.map Cell.width
  m.inputs.all (fun p => 0 < p.width) &&
  cellsValid (m.scope subs) m.cells &&
  m.regs.all (fun r => 0 < r.width && width r.next == some r.width &&
    match r.reset with | .none => true | .sync v => v < 2 ^ r.width) &&
  m.mems.all (fun mm => 0 < mm.addrWidth && 0 < mm.width && mm.writes.all fun p =>
    width p.en == some 1 && width p.addr == some mm.addrWidth && width p.data == some mm.width) &&
  m.outputs.all (fun o => (width o.node).isSome)

def Design.signatures (d : Design) : Array (List Nat × List Nat) :=
  d.modules.map fun m => (m.inWidths, m.outWidths)

/-- Each module is checked against the signatures of the modules before it. -/
def Design.check (d : Design) : Bool :=
  0 < d.modules.size &&
  (List.range d.modules.size).all fun k =>
    match d.modules[k]? with
    | some m => m.check (d.signatures.extract 0 k)
    | none => false

end HDLean.Rtl
