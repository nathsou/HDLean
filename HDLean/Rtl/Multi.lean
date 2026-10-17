import HDLean.Rtl.Design
import HDLean.Semantics.Clock

/-!
# Several clock domains

A multi-clock design is one list of modules (`design`) and, per clock domain,
the index of its top module. Domains interact only through

* **two-flop synchronizers** (`Crossing`): output `out` of domain `src`'s top,
  which must be driven directly by a register, is sampled by two flops clocked
  by domain `dst`. On a `dst` edge the first flop takes, bit by bit, the old or
  the new source value as an oracle mask says (`sampleBits`: mask bit set keeps
  the old bit), and the second flop takes the old first flop; both clear on
  `dst`'s reset;
* **shared memories** (`SharedMem`): written by domain `wdom` (enable, address
  and data are outputs of its top) on its edges, read asynchronously by domain
  `rdom` at an address driven directly by one of its registers.

Domain `d`'s top module sees, in order: its reset as input 0, its external
inputs, the second flops of the crossings into `d`, and the read words of the
memories it reads. Every state is a power-up state; edges, resets, inputs and
sampling masks are arbitrary per step.
-/
namespace HDLean.Rtl

structure Crossing where
  src : Nat
  out : Nat
  dst : Nat
  deriving Repr, DecidableEq, Inhabited

structure SharedMem where
  name : Ident
  addrWidth : Nat
  width : Nat
  wdom : Nat
  wen : Nat
  waddr : Nat
  wdata : Nat
  rdom : Nat
  raddr : Nat
  deriving Repr, DecidableEq, Inhabited

structure MDesign where
  design : Design
  tops : Array Nat
  crossings : Array Crossing
  mems : Array SharedMem
  deriving Repr, DecidableEq, Inhabited

namespace MDesign
variable (md : MDesign)

def topOf (d : Nat) : Nat := md.tops.getD d 0
def topModule (d : Nat) : Module := md.design.modules.getD (md.topOf d) default

/-- The register driving output `o` of domain `d`'s top, and its width. -/
def regOut (d o : Nat) : Nat × Nat :=
  let m := md.topModule d
  match m.outputs[o]? with
  | some op =>
    match m.cells[op.node]? with
    | some ⟨w, .reg r⟩ => (r, w)
    | _ => (0, 0)
  | none => (0, 0)

structure State where
  stores : Array Store
  first : Array Nat
  second : Array Nat
  mems : Array (Array Nat)

instance : Inhabited State := ⟨⟨#[], #[], #[], #[]⟩⟩

structure Event where
  ins : Array (Array Nat)
  rst : Array Bool
  edge : Array Bool
  /-- Per crossing, the sampling mask of its first flop (bit set: keep the old bit). -/
  mask : Array Nat

def Event.edgeOf (e : Event) (d : Nat) : Bool := e.edge.getD d false
def Event.rstOf (e : Event) (d : Nat) : Bool := e.rst.getD d false

def State.store (s : State) (d : Nat) : Store := s.stores.getD d default

/-- The value of the register behind output `o` of domain `d`, at its width. -/
def regValue (st : Store) (d o : Nat) : Nat := (bv (md.regOut d o).2 (st.regs.getD (md.regOut d o).1 0)).toNat

/-- Memories always have exactly `2 ^ addrWidth` words. -/
def shapeMem (aw : Nat) (old : Array Nat) : Array Nat :=
  if old.size = 2 ^ aw then old else Array.ofFn (n := 2 ^ aw) fun j => old.getD j.val 0

/-- Read word of shared memory `k`, at the address register of its reader. -/
def memRead (s : State) (k : Nat) : Nat :=
  let mm := md.mems.getD k default
  (s.mems.getD k #[]).getD (md.regValue (s.store mm.rdom) mm.rdom mm.raddr) 0

def syncIns (s : State) (d : Nat) : List Nat :=
  md.crossings.toList.zipIdx.filterMap fun p => if p.1.dst = d then some (s.second.getD p.2 0) else none

def memIns (s : State) (d : Nat) : List Nat :=
  md.mems.toList.zipIdx.filterMap fun p => if p.1.rdom = d then some (md.memRead s p.2) else none

/-- What domain `d`'s top module sees. -/
def domainIns (s : State) (e : Event) (d : Nat) : Array Nat :=
  #[(e.rstOf d).toNat] ++ e.ins.getD d #[] ++ (md.syncIns s d).toArray ++ (md.memIns s d).toArray

def semOf (s : State) (e : Event) (d : Nat) : Array Nat × Store :=
  md.design.sem (md.topOf d) (s.store d) (md.domainIns s e d) (e.rstOf d)

/-- Domain `d`'s outputs in this step (before its edge). -/
def outputs (s : State) (e : Event) (d : Nat) : Array Nat := (md.semOf s e d).1

def nextStore (s : State) (e : Event) (d : Nat) : Store :=
  if e.edgeOf d then (md.semOf s e d).2 else s.store d

def nextFirst (s : State) (e : Event) (k : Nat) (c : Crossing) : Nat :=
  if e.edgeOf c.dst then
    if e.rstOf c.dst then 0
    else
      let w := (md.regOut c.src c.out).2
      (sampleBits (bv w (md.regValue (s.store c.src) c.src c.out))
        (bv w (md.regValue (md.nextStore s e c.src) c.src c.out)) (bv w (e.mask.getD k 0))).toNat
  else s.first.getD k 0

def nextSecond (s : State) (e : Event) (k : Nat) (c : Crossing) : Nat :=
  if e.edgeOf c.dst then (if e.rstOf c.dst then 0 else s.first.getD k 0) else s.second.getD k 0

def nextMem (s : State) (e : Event) (k : Nat) (mm : SharedMem) : Array Nat :=
  let old := shapeMem mm.addrWidth (s.mems.getD k #[])
  if e.edgeOf mm.wdom then
    let o := md.outputs s e mm.wdom
    if (o.getD mm.wen 0).testBit 0 then old.setIfInBounds (o.getD mm.waddr 0) (bv mm.width (o.getD mm.wdata 0)).toNat
    else old
  else old

/-- One global step: every domain with an edge advances; synchronizers and memories follow. -/
def next (s : State) (e : Event) : State where
  stores := (Array.range md.tops.size).map (md.nextStore s e)
  first := md.crossings.mapIdx (md.nextFirst s e)
  second := md.crossings.mapIdx (nextSecond s e)
  mems := md.mems.mapIdx (md.nextMem s e)

def stateFrom (s₀ : State) (es : Nat → Event) : Nat → State
  | 0 => s₀
  | t + 1 => md.next (stateFrom s₀ es t) (es t)

/-! ## Well-formedness -/

def outWidth (d o : Nat) : Option Nat :=
  let m := md.topModule d
  (m.outputs[o]?).bind fun op => (m.cells[op.node]?).map Cell.width

def isRegOut (d o : Nat) : Bool :=
  let m := md.topModule d
  match (m.outputs[o]?).bind fun op => m.cells[op.node]? with
  | some ⟨_, .reg _⟩ => true
  | _ => false

/-- Input widths that domain `d`'s top must have, after its external inputs. -/
def extraWidths (d : Nat) : List Nat :=
  (md.crossings.toList.filter (·.dst = d)).map (fun c => (md.regOut c.src c.out).2) ++
  (md.mems.toList.filter (·.rdom = d)).map SharedMem.width

def check : Bool :=
  md.design.check && 0 < md.tops.size &&
  md.tops.all (· < md.design.modules.size) &&
  (List.range md.tops.size).all (fun d =>
    let ws := (md.topModule d).inWidths
    ws.head? == some 1 && (md.extraWidths d).length + 1 ≤ ws.length &&
      ws.drop (ws.length - (md.extraWidths d).length) == md.extraWidths d) &&
  md.crossings.all (fun c => c.src < md.tops.size && c.dst < md.tops.size && md.isRegOut c.src c.out &&
    0 < (md.regOut c.src c.out).2) &&
  md.mems.all (fun mm => mm.wdom < md.tops.size && mm.rdom < md.tops.size && 0 < mm.width &&
    md.outWidth mm.wdom mm.wen == some 1 && md.outWidth mm.wdom mm.waddr == some mm.addrWidth &&
    md.outWidth mm.wdom mm.wdata == some mm.width && md.isRegOut mm.rdom mm.raddr &&
    (md.regOut mm.rdom mm.raddr).2 == mm.addrWidth)

end MDesign

end HDLean.Rtl
