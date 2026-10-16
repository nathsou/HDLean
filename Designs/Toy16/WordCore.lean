import Designs.Toy16.WordAlu

/-!
# The core's cycle, as functions of words

`Hw.*` restate the core's wiring as functions of the instruction, the register
record, the two memories and the ALU's output; `cpuBody_ensures` shows the
built module computes exactly these. Relating them to the ISA is a separate,
purely arithmetic step (`WordRefinement.lean`).
-/
namespace HDLean.Toy16.Word
open HDLean.Rtl HDLean.Rtl.Build

namespace Hw

def opc (i : Word) : BitVec 4 := i.extractLsb' 12 4
def rd (i : Word) : BitVec 3 := i.extractLsb' 9 3
def rs (i : Word) : BitVec 3 := i.extractLsb' 6 3
def rt (i : Word) : BitVec 3 := i.extractLsb' 3 3
def imm (i : Word) : BitVec 6 := i.extractLsb' 0 6
def off (i : Word) : Addr := i.extractLsb' 0 8

/-- `1` when the register index is zero. -/
def isZ (x : BitVec 3) : BitVec 1 := BitVec.ofBool (CmpOp.eval .eq x 0)
/-- A register read where register zero reads as zero. -/
def readZ (rf : BitVec 3 → Word) (x : BitVec 3) : Word := if (isZ x).getLsbD 0 then 0 else rf x

def a (i : Word) (rf : BitVec 3 → Word) : Word := readZ rf (rs i)
def b (i : Word) (rf : BitVec 3 → Word) : Word := readZ rf (rt i)
def v (i : Word) (rf : BitVec 3 → Word) : Word := readZ rf (rd i)
def immS (i : Word) : Word := (imm i).signExtend 16
def isOp (i : Word) (k : BitVec 4) : BitVec 1 := BitVec.ofBool (CmpOp.eval .eq (opc i) k)
def bsel (i : Word) (rf : BitVec 3 → Word) : Word := if (isOp i 6).getLsbD 0 then immS i else b i rf
def ea (i : Word) (rf : BitVec 3 → Word) : Addr := (a i rf + immS i).extractLsb' 0 8
def isAlu (i : Word) : BitVec 1 := BitVec.ofBool (CmpOp.eval .ult (opc i) 7)
def isHalt (i : Word) : BitVec 1 := BitVec.ofBool (CmpOp.eval .ult 10 (opc i))
def wbd (i : Word) (rf : BitVec 3 → Word) (dm : Addr → Word) (y : Word) : Word :=
  if (isOp i 7).getLsbD 0 then dm (ea i rf) else y
def wbe (i : Word) : BitVec 1 := (isAlu i ||| isOp i 7) &&& ~~~(isZ (rd i))
def pc1 (r : CpuRegs BitVec) : Addr := r.pc + 1
def npc (i : Word) (r : CpuRegs BitVec) (rf : BitVec 3 → Word) : Addr :=
  if (isOp i 10).getLsbD 0 then pc1 r + off i
  else if (isOp i 9 &&& BitVec.ofBool (CmpOp.eval .eq (v i rf) (a i rf))).getLsbD 0 then pc1 r + (imm i).signExtend 8
  else if (isHalt i).getLsbD 0 then r.pc else pc1 r
def live (r : CpuRegs BitVec) : BitVec 1 := ~~~r.halted

/-- The next register record. -/
def next (i : Word) (r : CpuRegs BitVec) (rf : BitVec 3 → Word) (dm : Addr → Word) (y : Word) : CpuRegs BitVec :=
  ⟨if (live r).getLsbD 0 then npc i r rf else r.pc, r.halted ||| isHalt i, live r, r.pc, i, npc i r rf, wbe i,
    rd i, wbd i rf dm y, isOp i 8, ea i rf, v i rf, isHalt i⟩

/-- The outputs: fetch address and the registered report. -/
def out (r : CpuRegs BitVec) : CpuOut BitVec :=
  ⟨r.pc, r.valid, r.rpc, r.rinstr, r.rnext, r.wbv, r.wbr, r.wbval, r.stv, r.sta, r.stval, r.rhalt⟩

end Hw

/-! ## Reading the environment -/

def instrOf (e : Env) : Word := (Bundle.decode CpuIn (e.ins.getD · 0)).instr
def regsOf (e : Env) : CpuRegs BitVec := Bundle.decode CpuRegs (e.st.regs.getD · 0)
def rfOf (e : Env) : BitVec 3 → Word := e.st.mem 0 3 16
def dmOf (e : Env) : Addr → Word := e.st.mem 1 8 16

/-- The ALU instance's output, its store being slot `k`. -/
def aluOf (k : Nat) (e : Env) : Word :=
  (unpack [16] (e.sem 0 (e.st.subs.getD k default)
    #[(Hw.opc (instrOf e)).toNat, (Hw.a (instrOf e) (rfOf e)).toNat, (Hw.bsel (instrOf e) (rfOf e)).toNat]
    e.rst).1.toList).head

def rfWrite (k : Nat) : WriteSpec 3 16 :=
  ⟨fun e => (Hw.live (regsOf e) &&& Hw.wbe (instrOf e)).getLsbD 0, fun e => Hw.rd (instrOf e),
   fun e => Hw.wbd (instrOf e) (rfOf e) (dmOf e) (aluOf k e)⟩

def dmWrite : WriteSpec 8 16 :=
  ⟨fun e => (Hw.live (regsOf e) &&& Hw.isOp (instrOf e) 8).getLsbD 0, fun e => Hw.ea (instrOf e) (rfOf e),
   fun e => Hw.v (instrOf e) (rfOf e)⟩

theorem cpuCtx_ok : cpuCtx.ok = true := by decide

end HDLean.Toy16.Word
