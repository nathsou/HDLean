import Designs.Toy16.Spec
namespace HDLean.Toy16

def alu (op rd rs rt : Nat) : Word := BitVec.ofNat 16 (op * 4096 + rd * 512 + rs * 64 + rt * 8)
def immediate (op rd rs : Nat) (imm : Int) : Word :=
  BitVec.ofNat 16 (op * 4096 + rd * 512 + rs * 64 + (BitVec.ofInt 6 imm).toNat)
def jump (off : Int) : Word := BitVec.ofNat 16 (10 * 4096 + (BitVec.ofInt 12 off).toNat)

/-- Sum 5+4+3+2+1, store at address zero, and halt. -/
def sumProgram (a : Addr) : Word := match a.toNat with
  | 0 => immediate 6 2 0 0
  | 1 => immediate 6 1 0 5
  | 2 => alu 0 2 2 1
  | 3 => immediate 6 1 1 (-1)
  | 4 => immediate 9 1 0 1
  | 5 => jump (-4)
  | 6 => immediate 8 2 0 0
  | _ => 0xF000

set_option maxRecDepth 4096 in
example : let s := run sumProgram (ArchState.atReset (fun _ => 0xAAAA) (fun _ => 0x5555)) 23
    s.halted = true ∧ s.dmem 0 = 15 ∧ s.pc = 7 := by decide

example : (effectWord (immediate 6 0 0 5) (ArchState.atReset (fun _ => 0) (fun _ => 0))).wb = none := by decide
example : (effectWord 0xB000 (ArchState.atReset (fun _ => 0) (fun _ => 0))).halt = true := by decide
end HDLean.Toy16
