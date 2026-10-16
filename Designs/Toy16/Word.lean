import HDLean.Rtl.Memory
import HDLean.Rtl.Instance
import Designs.Toy16.Spec

/-!
# Toy16 on word-level RTL

A single-cycle Toy16 core built from words: the register file and the data
memory are RTL memories, the ALU is a separate module instantiated by the core,
and the state is a typed record. The instruction bus is an input: the core
shows its fetch address `pc`, and the environment answers with the
instruction at that address in the same cycle. Each executed instruction is
reported on the registered retirement outputs one cycle later.
-/
namespace HDLean.Toy16.Word
open HDLean.Rtl HDLean.Rtl.Build

/-! ## ALU -/

hdl_record AluIn where
  op : 4
  a : 16
  b : 16

hdl_record AluOut where
  y : 16

/-- What the ALU computes for opcodes 0–6 (6 is add-immediate: the core passes
the immediate as `b`). -/
def aluSpec (op : BitVec 4) (a b : Word) : Word :=
  match op.toNat with
  | 0 => a + b
  | 1 => a - b
  | 2 => a &&& b
  | 3 => a ||| b
  | 4 => a ^^^ b
  | 5 => if a < b then 1 else 0
  | _ => a + b

def aluCtx : Ctx := Ctx.mealy "alu" AluIn AluOut NoFields ⟨⟩

def aluBody (i : AluIn Sig) (_ : NoFields Sig) : M aluCtx (Step AluOut NoFields) := do
  let s ← add i.a i.b
  let d ← sub i.a i.b
  let n ← and i.a i.b
  let o ← or i.a i.b
  let x ← xor i.a i.b
  let lt1 ← ult i.a i.b
  let lt ← zext lt1 16
  let o0 ← slice i.op 0 1
  let o1 ← slice i.op 1 1
  let o2 ← slice i.op 2 1
  let m01 ← mux o0 d s
  let m23 ← mux o0 o n
  let m45 ← mux o0 lt x
  let lo ← mux o1 m23 m01
  let hi ← mux o1 s m45
  let y ← mux o2 hi lo
  pure { out := ⟨y⟩, next := ⟨⟩ }

def aluModule : Module := aluCtx.module (mealy AluIn AluOut NoFields aluBody)

/-! ## Core -/

hdl_record CpuIn where
  instr : 16

/-- Fetch address, then the retirement report of the previous cycle. -/
hdl_record CpuOut where
  pc : 8
  valid : 1
  rpc : 8
  rinstr : 16
  rnext : 8
  wbv : 1
  wbr : 3
  wbval : 16
  stv : 1
  sta : 8
  stval : 16
  halt : 1

hdl_record CpuRegs where
  pc : 8
  halted : 1
  valid : 1
  rpc : 8
  rinstr : 16
  rnext : 8
  wbv : 1
  wbr : 3
  wbval : 16
  stv : 1
  sta : 8
  stval : 16
  rhalt : 1

/-- Reset clears the control state only; memories and the report are free. -/
def resets : CpuRegs (fun _ => Reset) :=
  ⟨.sync 0, .sync 0, .sync 0, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none⟩

def cpuMems : Array MemSpec := #[⟨"rf", 3, 16, 1⟩, ⟨"dmem", 8, 16, 1⟩]

def cpuCtx : Ctx := Ctx.mealy "toy16" CpuIn CpuOut CpuRegs resets cpuMems #[([4, 16, 16], [16])]

def cpuBody (i : CpuIn Sig) (r : CpuRegs Sig) : M cpuCtx (Step CpuOut CpuRegs) := do
  let w := i.instr
  -- decode
  let opc ← slice w 12 4
  let rd ← slice w 9 3
  let rs ← slice w 6 3
  let rt ← slice w 3 3
  let imm ← slice w 0 6
  let off ← slice w 0 8
  -- operands; register zero reads as zero
  let z3 ← const 3 0
  let z16 ← const 16 0
  let ra ← memRead 0 16 rs
  let rsz ← eq rs z3
  let a ← mux rsz z16 ra
  let rb ← memRead 0 16 rt
  let rtz ← eq rt z3
  let b ← mux rtz z16 rb
  let rv ← memRead 0 16 rd
  let rdz ← eq rd z3
  let v ← mux rdz z16 rv
  let immS ← sext imm 16
  -- execute
  let c6 ← const 4 6
  let isAddi ← eq opc c6
  let bsel ← mux isAddi immS b
  let alu ← instantiate 0 [4, 16, 16] [16] (.cons opc (.cons a (.cons bsel .nil)))
  let eaw ← add a immS
  let ea ← slice eaw 0 8
  let ld ← memRead 1 16 ea
  -- control
  let c7 ← const 4 7
  let c8 ← const 4 8
  let c9 ← const 4 9
  let c10 ← const 4 10
  let isAlu ← ult opc c7
  let isLoad ← eq opc c7
  let isStore ← eq opc c8
  let isBeq ← eq opc c9
  let isJmp ← eq opc c10
  let isHalt ← ult c10 opc
  let wbd ← mux isLoad ld alu.head
  let wbk ← or isAlu isLoad
  let rdnz ← not rdz
  let wbe ← and wbk rdnz
  -- next pc
  let one ← const 8 1
  let pc1 ← add r.pc one
  let imm8 ← sext imm 8
  let br ← add pc1 imm8
  let jt ← add pc1 off
  let tk ← eq v a
  let btk ← and isBeq tk
  let n1 ← mux isHalt r.pc pc1
  let n2 ← mux btk br n1
  let npc ← mux isJmp jt n2
  -- commit, unless halted
  let live ← not r.halted
  let pcN ← mux live npc r.pc
  let haltN ← or r.halted isHalt
  let rfEn ← and live wbe
  let dmEn ← and live isStore
  pure { out := ⟨r.pc, r.valid, r.rpc, r.rinstr, r.rnext, r.wbv, r.wbr, r.wbval, r.stv, r.sta, r.stval, r.rhalt⟩
         next := ⟨pcN, haltN, live, r.pc, w, npc, wbe, rd, wbd, isStore, ea, v, isHalt⟩
         writes := #[#[port rfEn rd wbd], #[port dmEn ea v]] }

def cpuModule : Module := cpuCtx.module (mealy CpuIn CpuOut CpuRegs cpuBody)

/-- The ALU is module 0, the core module 1 (the top). -/
def design : Design := ⟨#[aluModule, cpuModule]⟩

end HDLean.Toy16.Word
