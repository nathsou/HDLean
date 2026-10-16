import Designs.Toy16.DagWords
import Designs.Toy16.Hardware
import HDLean.Netlist.DagLower

set_option linter.constructorNameAsVariable false
namespace HDLean.Toy16.DagPhysical
open Dag.Build

/-- The complete CPU datapath allocates each named shared result once. Memory
reads are balanced trees; all 4,288 state bits remain explicit registers. -/
structure Datapath where
  zero : Ref
  one : Ref
  words : Vector (Dag.Build.Word 16) 268
  pc : Dag.Build.Word 8
  halted : Ref
  execute : Ref
  fetched : Dag.Build.Word 16
  rd : Dag.Build.Word 3
  imm : Dag.Build.Word 6
  offset : Dag.Build.Word 12
  opcode : Dag.Build.Word 4
  operandA : Dag.Build.Word 16
  storeData : Dag.Build.Word 16
  addedImmediate : Dag.Build.Word 16
  ea : Dag.Build.Word 8
  opTests : Vector Ref 11
  trap : Ref
  flagTrap : Dag.Build.Word 16
  flagExecute : Dag.Build.Word 16
  result : Dag.Build.Word 16

structure Control where
  base : Datapath
  nextPc : Dag.Build.Word 8
  writeEnable : Ref
  active : Ref
  fetchEnable : Ref
  fetchValue : Dag.Build.Word 16

def datapath : M 0 0 (268*16) Datapath := do
  let zero ← literal false
  let one ← literal true
  let words ← tabulate fun j : Fin 268 => Dag.Build.Word.registers (j.val*16) (by omega)
  let z16 : Dag.Build.Word 16 := Vector.replicate 16 zero
  let pc := Dag.Build.Word.extract words[0] 0 8 (by decide)
  let halted := words[1][0]
  let execute := words[2][0]
  let fetched := words[3]
  let rd := Dag.Build.Word.extract fetched 9 3 (by decide)
  let rs := Dag.Build.Word.extract fetched 6 3 (by decide)
  let rt := Dag.Build.Word.extract fetched 3 3 (by decide)
  let opcode := Dag.Build.Word.extract fetched 12 4 (by decide)
  let imm := Dag.Build.Word.extract fetched 0 6 (by decide)
  let offset := Dag.Build.Word.extract fetched 0 12 (by decide)
  let regTable := fun j : Fin 8 => if j.val = 0 then z16 else words[4+j.val]'(by omega)
  let operandA ← Dag.Build.Word.selectBalanced rs regTable
  let operandB ← Dag.Build.Word.selectBalanced rt regTable
  let storeData ← Dag.Build.Word.selectBalanced rd regTable
  let addedImmediate ← Dag.Build.Word.add zero operandA (Dag.Build.Word.signExtend zero imm 16)
  let ea := Dag.Build.Word.setWidth zero addedImmediate 8
  let opTests ← tabulate fun j : Fin 11 => do Dag.Build.Word.equal one opcode (← Dag.Build.Word.literal (BitVec.ofNat 4 j.val))
  let trap ← inv (← Dag.Build.Word.ult one opcode (← Dag.Build.Word.literal 11))
  let addResult ← Dag.Build.Word.add zero operandA operandB
  let subResult ← Dag.Build.Word.sub one operandA operandB
  let andResult ← Dag.Build.Word.bitAnd operandA operandB
  let orResult ← Dag.Build.Word.bitOr operandA operandB
  let xorResult ← Dag.Build.Word.bitXor operandA operandB
  let less ← Dag.Build.Word.ult one operandA operandB
  let one16 ← Dag.Build.Word.literal (1 : BitVec 16)
  let flagWord := fun b => Dag.Build.Word.mux b one16 z16
  let flagLess ← flagWord less
  let flagTrap ← flagWord trap
  let flagExecute ← flagWord (← inv execute)
  let memResult ← Dag.Build.Word.selectBalanced ea fun j : Fin 256 => words[12+j.val]'(by omega)
  let result ← Dag.Build.Word.selectBalanced opcode fun j => match j.val with
    | 0 => addResult | 1 => subResult | 2 => andResult | 3 => orResult
    | 4 => xorResult | 5 => flagLess | 6 => addedImmediate | 7 => memResult
    | _ => z16
  pure ⟨zero,one,words,pc,halted,execute,fetched,rd,imm,offset,opcode,operandA,storeData,addedImmediate,ea,opTests,trap,flagTrap,flagExecute,result⟩

def control (imem : Addr → Word) (base : Datapath) : M 0 0 (268*16) Control := do
  let zero := base.zero
  let one := base.one
  let words := base.words
  let pc := base.pc
  let halted := base.halted
  let execute := base.execute
  let fetched := base.fetched
  let rd := base.rd
  let imm := base.imm
  let offset := base.offset
  let opcode := base.opcode
  let operandA := base.operandA
  let storeData := base.storeData
  let addedImmediate := base.addedImmediate
  let ea := base.ea
  let opTests := base.opTests
  let trap := base.trap
  let flagTrap := base.flagTrap
  let flagExecute := base.flagExecute
  let result := base.result
  let pc1 ← Dag.Build.Word.add zero pc (← Dag.Build.Word.literal 1)
  let jumpPc ← Dag.Build.Word.add zero pc1 (Dag.Build.Word.setWidth zero offset 8)
  let branchPc ← Dag.Build.Word.add zero pc1 (Dag.Build.Word.signExtend zero imm 8)
  let branch ← and opTests[9] (← Dag.Build.Word.equal one storeData operandA)
  let nextPc ← Dag.Build.Word.mux trap pc (← Dag.Build.Word.mux opTests[10] jumpPc (← Dag.Build.Word.mux branch branchPc pc1))
  let writeEnable ← and (← Dag.Build.Word.ult one opcode (← Dag.Build.Word.literal 8))
    (← inv (← Dag.Build.Word.equal one rd (← Dag.Build.Word.literal 0)))
  let active ← and execute (← inv halted)
  let fetchEnable ← and (← inv halted) (← inv execute)
  let rom ← tabulate fun a : Fin 256 => Dag.Build.Word.literal (imem (BitVec.ofNat 8 a.val))
  let fetchValue ← Dag.Build.Word.selectBalanced pc fun a => rom[a]
  pure ⟨base,nextPc,writeEnable,active,fetchEnable,fetchValue⟩

def packOutputs {α : Type} (active : α) (pc : Vector α 8) (fetched : Vector α 16)
    (nextPc : Vector α 8) (writeEnable : α) (rd : Vector α 3) (result : Vector α 16)
    (storeEnable : α) (ea : Vector α 8) (storeData : Vector α 16) (trap : α) : Vector α 79 := Vector.ofFn fun k =>
    if h : k.val = 0 then active
    else if h : k.val < 9 then pc[k.val-1]'(by omega)
    else if h : k.val < 25 then fetched[k.val-9]'(by omega)
    else if h : k.val < 33 then nextPc[k.val-25]'(by omega)
    else if h : k.val = 33 then writeEnable
    else if h : k.val < 37 then rd[k.val-34]'(by omega)
    else if h : k.val < 53 then result[k.val-37]'(by omega)
    else if h : k.val = 53 then storeEnable
    else if h : k.val < 62 then ea[k.val-54]'(by omega)
    else if h : k.val < 78 then storeData[k.val-62]'(by omega)
    else trap

def ports (c : Control) : M 0 0 (268*16) (Vector Ref (268*16) × Vector Ref 79) := do
  let zero := c.base.zero
  let one := c.base.one
  let words := c.base.words
  let pc := c.base.pc
  let halted := c.base.halted
  let execute := c.base.execute
  let fetched := c.base.fetched
  let rd := c.base.rd
  let imm := c.base.imm
  let offset := c.base.offset
  let opcode := c.base.opcode
  let operandA := c.base.operandA
  let storeData := c.base.storeData
  let addedImmediate := c.base.addedImmediate
  let ea := c.base.ea
  let opTests := c.base.opTests
  let trap := c.base.trap
  let flagTrap := c.base.flagTrap
  let flagExecute := c.base.flagExecute
  let result := c.base.result
  let nextPc := c.nextPc
  let writeEnable := c.writeEnable
  let active := c.active
  let fetchEnable := c.fetchEnable
  let fetchValue := c.fetchValue
  let nextWords ← tabulate fun j : Fin 268 => do
    if j.val = 0 then Dag.Build.Word.mux active (Dag.Build.Word.setWidth zero nextPc 16) words[j]
    else if j.val = 1 then Dag.Build.Word.mux active flagTrap words[j]
    else if j.val = 2 then Dag.Build.Word.mux halted words[j] flagExecute
    else if j.val = 3 then Dag.Build.Word.mux fetchEnable fetchValue words[j]
    else if j.val < 12 then
      Dag.Build.Word.mux (← and active (← and writeEnable (← Dag.Build.Word.equal one rd (← Dag.Build.Word.literal (BitVec.ofNat 3 (j.val-4)))))) result words[j]
    else Dag.Build.Word.mux (← and active (← and opTests[8] (← Dag.Build.Word.equal one ea (← Dag.Build.Word.literal (BitVec.ofNat 8 (j.val-12)))))) storeData words[j]
  let outputs := packOutputs active pc fetched nextPc writeEnable rd result opTests[8] ea storeData trap
  pure (nextWords.flatten,outputs)

def program (imem : Addr → Word) : M 0 0 (268*16) (Vector Ref (268*16) × Vector Ref 79) := do
  let data ← datapath
  let controls ← control imem data
  ports controls

def resetKinds : Vector ResetKind (268*16) :=
  Vector.ofFn fun k => if k.val / 16 < 3 then .synchronous false else .hold

/-- This constructor checks only reference bounds. Semantic refinement is exposed
separately, so unsuccessful construction can never silently produce a circuit. -/
def hardware? (imem : Addr → Word) : Option (Dag 0 0 (268*16) 79) :=
  Dag.Build.run "toy16" resetKinds (program imem)

end HDLean.Toy16.DagPhysical
