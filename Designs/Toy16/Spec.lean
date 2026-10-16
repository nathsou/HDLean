import HDLean.Semantics.Retirement
namespace HDLean.Toy16
abbrev Word := BitVec 16
abbrev Addr := BitVec 8
abbrev Reg := BitVec 3

/-- Architectural effects exposed at retirement, including stores and halt. -/
structure Retire where
  pc : Addr
  instr : Word
  nextPc : Addr
  wb : Option (Reg × Word)
  store : Option (Addr × Word)
  halt : Bool
  deriving Repr, DecidableEq, BEq

/-- The architectural model deliberately leaves registers and memory unconstrained at reset. -/
structure ArchState where
  pc : Addr
  regs : Reg → Word
  dmem : Addr → Word
  halted : Bool

/-- Register zero ignores its physical contents. -/
def ArchState.read (s : ArchState) (r : Reg) : Word := if r = 0 then 0 else s.regs r
/-- Reset changes control only. -/
def ArchState.atReset (regs : Reg → Word) (dmem : Addr → Word) : ArchState := ⟨0, regs, dmem, false⟩

/-- Decode and execute one Toy16 instruction. Opcodes 11–14 trap by halting. -/
def effectWord (w : Word) (s : ArchState) : Retire :=
  let rd : Reg := w.extractLsb' 9 3
  let rs : Reg := w.extractLsb' 6 3
  let rt : Reg := w.extractLsb' 3 3
  let imm : BitVec 6 := w.extractLsb' 0 6
  let off : BitVec 12 := w.extractLsb' 0 12
  let base : Retire := ⟨s.pc, w, s.pc + 1, none, none, false⟩
  let wr (v : Word) := if rd = 0 then none else some (rd, v)
  let a := s.read rs
  let b := s.read rt
  let ea : Addr := (a + imm.signExtend 16).setWidth 8
  match (w.extractLsb' 12 4).toNat with
  | 0 => { base with wb := wr (a + b) }
  | 1 => { base with wb := wr (a - b) }
  | 2 => { base with wb := wr (a &&& b) }
  | 3 => { base with wb := wr (a ||| b) }
  | 4 => { base with wb := wr (a ^^^ b) }
  | 5 => { base with wb := wr (if a < b then 1 else 0) }
  | 6 => { base with wb := wr (a + imm.signExtend 16) }
  | 7 => { base with wb := wr (s.dmem ea) }
  | 8 => { base with store := some (ea, s.read rd) }
  | 9 => { base with nextPc := if s.read rd = a then s.pc + 1 + imm.signExtend 8 else s.pc + 1 }
  | 10 => { base with nextPc := s.pc + 1 + off.setWidth 8 }
  | _ => { base with nextPc := s.pc, halt := true }

/-- Fetch from the immutable program image and compute the next architectural event. -/
def effect (imem : Addr → Word) (s : ArchState) := effectWord (imem s.pc) s
/-- Apply the externally observable effect to the architectural state. -/
def applyEffect (s : ArchState) (r : Retire) : ArchState :=
  { pc := r.nextPc, halted := r.halt
    regs := fun k => match r.wb with | some (rd, v) => if k = rd then v else s.regs k | none => s.regs k
    dmem := fun k => match r.store with | some (a, v) => if k = a then v else s.dmem k | none => s.dmem k }
/-- A halted ISA stays halted. -/
def step (imem : Addr → Word) (s : ArchState) := if s.halted then s else applyEffect s (effect imem s)
/-- Execute n instructions. -/
def run (imem : Addr → Word) (s : ArchState) (n : Nat) := iterate (step imem) s n
/-- Reference retirement stream. -/
def isaRetire (imem : Addr → Word) (s : ArchState) (n : Nat) := effect imem (run imem s n)
end HDLean.Toy16
