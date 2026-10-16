import HDLean.Rtl.Syntax
import HDLean.Semantics.Machine

/-!
Cycle semantics of word-level RTL.

Values are natural numbers read at a width through `BitVec.ofNat`, so every
operator is literally the corresponding `BitVec` operation (division by zero
included: `x / 0 = 0`, `x % 0 = x`).

The state of a module instance is a `Store`: its registers, its memories and
the stores of its sub-instances. Every store is meaningful: missing entries read
as zero and the next store always has the declared shape, so quantifying over
all stores is quantifying over all power-up states.
-/
namespace HDLean.Rtl

inductive Store where
  | mk (regs : Array Nat) (mems : Array (Array Nat)) (subs : Array Store)

instance : Inhabited Store := ⟨.mk #[] #[] #[]⟩

namespace Store
def regs : Store → Array Nat | .mk r _ _ => r
def mems : Store → Array (Array Nat) | .mk _ m _ => m
def subs : Store → Array Store | .mk _ _ s => s
@[simp] theorem regs_mk : (Store.mk r m s).regs = r := rfl
@[simp] theorem mems_mk : (Store.mk r m s).mems = m := rfl
@[simp] theorem subs_mk : (Store.mk r m s).subs = s := rfl
end Store

/-- Read a raw value at a width. -/
abbrev bv (w v : Nat) : BitVec w := BitVec.ofNat w v

def BinOp.eval : BinOp → BitVec w → BitVec w → Nat → BitVec w
  | .and, x, y, _ => x &&& y
  | .or, x, y, _ => x ||| y
  | .xor, x, y, _ => x ^^^ y
  | .nand, x, y, _ => ~~~(x &&& y)
  | .nor, x, y, _ => ~~~(x ||| y)
  | .xnor, x, y, _ => ~~~(x ^^^ y)
  | .add, x, y, _ => x + y
  | .sub, x, y, _ => x - y
  | .mul, x, y, _ => x * y
  | .udiv, x, y, _ => x / y
  | .umod, x, y, _ => x % y
  | .shl, x, _, n => x <<< n
  | .lshr, x, _, n => x >>> n
  | .ashr, x, _, n => x.sshiftRight n

def CmpOp.eval : CmpOp → BitVec w → BitVec w → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .ult, x, y => x.ult y
  | .ule, x, y => x.ule y
  | .slt, x, y => x.slt y
  | .sle, x, y => x.sle y

/-- Everything a cell can read in one cycle. -/
structure Frame where
  /-- Value of each earlier cell (always reduced to that cell's width). -/
  val : Nat → Nat
  input : Nat → Nat
  reg : Nat → Nat
  mem : Nat → Nat → Nat

/-- The value of a non-instance cell of width `w`, as a bit-vector. Operand
widths that matter are part of the operation, so a cell depends only on the
values of earlier cells. -/
def Op.evalBV (f : Frame) (w : Nat) : Op → BitVec w
  | .const v => bv w v
  | .input k => bv w (f.input k)
  | .reg k => bv w (f.reg k)
  | .memRead mi a => bv w (f.mem mi (f.val a))
  | .not a => ~~~(bv w (f.val a))
  | .neg a => -(bv w (f.val a))
  | .bin op a b => op.eval (bv w (f.val a)) (bv w (f.val b)) (f.val b)
  | .cmp op cw a b => (BitVec.ofBool (op.eval (bv cw (f.val a)) (bv cw (f.val b)))).setWidth w
  | .mux s a b => if (f.val s).testBit 0 then bv w (f.val a) else bv w (f.val b)
  | .slice a lo => bv w (f.val a >>> lo)
  | .concat h l lw => ((bv (w - lw) (f.val h)) ++ (bv lw (f.val l))).setWidth w
  | .zext a => bv w (f.val a)
  | .sext a fw => (bv fw (f.val a)).signExtend w
  | .inst .. => 0

/-- Pack outputs, first in the least significant bits. -/
def pack : List Nat → List Nat → Nat
  | w :: ws, v :: vs => v % 2 ^ w + 2 ^ w * pack ws vs
  | _, _ => 0

/-- One cycle of one module instance: outputs and next store. Reset is a plain
input that only affects registers. -/
abbrev Sem := Store → Array Nat → Bool → Array Nat × Store

def nullSem : Sem := fun _ _ _ => (#[], default)

/-- Values of the cells evaluated so far and the next stores of the instances. -/
structure Acc where
  vals : Array Nat
  subs : Array Store

def frame (st : Store) (ins : Array Nat) (vals : Array Nat) : Frame :=
  ⟨(vals.getD · 0), (ins.getD · 0), (st.regs.getD · 0), fun mi a => (st.mems.getD mi #[]).getD a 0⟩

/-- Evaluate one cell. -/
def stepCell (env : Nat → Sem) (st : Store)
    (ins : Array Nat) (rst : Bool) (acc : Acc) (c : Cell) : Acc :=
  match c.op with
  | .inst j args outs =>
    let r := env j (st.subs.getD acc.subs.size default) (args.toArray.map (acc.vals.getD · 0)) rst
    ⟨acc.vals.push (bv c.width (pack outs r.1.toList)).toNat, acc.subs.push r.2⟩
  | op => ⟨acc.vals.push (op.evalBV (frame st ins acc.vals) c.width).toNat, acc.subs⟩

def Reg.update (rst : Bool) (v : Nat → Nat) (r : Reg) : Nat :=
  match r.reset with
  | .sync x => if rst then (bv r.width x).toNat else (bv r.width (v r.next)).toNat
  | .none => (bv r.width (v r.next)).toNat

/-- Memories always come out with exactly `2 ^ addrWidth` entries. -/
def Mem.shape (mm : Mem) (old : Array Nat) : Array Nat :=
  if old.size = 2 ^ mm.addrWidth then old
  else Array.ofFn (n := 2 ^ mm.addrWidth) fun j => old.getD j.val 0

def Mem.update (v : Nat → Nat) (mm : Mem) (old : Array Nat) : Array Nat :=
  mm.writes.foldl (fun arr p =>
    if (v p.en).testBit 0 then arr.setIfInBounds (v p.addr) (bv mm.width (v p.data)).toNat else arr)
    (mm.shape old)

def Module.values (env : Nat → Sem) (m : Module) (st : Store) (ins : Array Nat) (rst : Bool) : Acc :=
  m.cells.foldl (stepCell env st ins rst) ⟨#[], #[]⟩

/-- The semantics of a module, given the semantics of the modules it instantiates. -/
def Module.evalWith (env : Nat → Sem) (m : Module) : Sem := fun st ins rst =>
  let acc := m.values env st ins rst
  let v := (acc.vals.getD · 0)
  (m.outputs.map (fun o => v o.node),
   .mk (m.regs.map (Reg.update rst v))
     (m.mems.mapIdx fun i mm => mm.update v (st.mems.getD i #[])) acc.subs)

namespace Design

/-- Module `k` sees only the modules before it. -/
def sem (d : Design) (k : Nat) : Sem :=
  match d.modules[k]? with
  | some m => m.evalWith (fun j => if j < k then d.sem j else nullSem)
  | none => nullSem
termination_by k

def env (d : Design) (k : Nat) : Nat → Sem := fun j => if j < k then d.sem j else nullSem

theorem sem_eq (d : Design) (k : Nat) (m : Module) (h : d.modules[k]? = some m) :
    d.sem k = m.evalWith (d.env k) := by
  rw [sem]; simp only [h]; rfl

def top (d : Design) : Nat := d.modules.size - 1

def step (d : Design) (st : Store) (x : Array Nat × Bool) : Store := (d.sem d.top st x.1 x.2).2

def output (d : Design) (st : Store) (ins : Array Nat) : Array Nat := (d.sem d.top st ins false).1

/-- Outputs do not depend on the current inputs. -/
def IsMoore (d : Design) : Prop := ∀ st a b, d.output st a = d.output st b

/-- Hardware view: arbitrary power-up store; inputs are (port values, reset). -/
def denote (d : Design) (_ : d.IsMoore) : PMachine Store (Array Nat × Bool) (Array Nat) :=
  ⟨fun s => d.output s #[], d.step⟩

end Design

end HDLean.Rtl
